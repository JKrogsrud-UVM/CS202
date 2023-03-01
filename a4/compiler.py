from typing import Set, Dict
import itertools
import sys
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86
import constants
import cif
from interference_graph import InterferenceGraph

comparisons = ['eq', 'gt', 'gte', 'lt', 'lte']
gensym_num = 0
global_logging = False


def log(label, value):
    if global_logging:
        print()
        print(f'--------------------------------------------------')
        print(f'Logging: {label}')
        print(value)
        print(f'--------------------------------------------------')


def log_ast(label, value):
    log(label, print_ast(value))


def gensym(x):
    """
    Constructs a new variable name guaranteed to be unique.
    :param x: A "base" variable name (e.g. "x")
    :return: A unique variable name (e.g. "x_1")
    """

    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


##################################################
# typecheck
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Expr  ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts)
# Stmts ::= List[Stmt]
# LVar  ::= Program(Stmts)

TEnv = Dict[str, type]


def typecheck(program: Program) -> Program:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param program: The Lif program to typecheck
    :return: The program, if it is well-typed
    """

    def tc_exp(e: Expr, env: TEnv) -> type:
        match e:
            case Var(x):
                if x in env:
                    return env[x]
                else:
                    raise Exception('Variable never assigned a value', x)
            case Constant(n):
                return type(n)
            case Prim("add", [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return int
            case Prim("sub", [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return int
            case Prim("not", [e1, e2]):
                assert tc_exp(e1, env) == tc_exp(e2, env)
                return bool
            case Prim("or", [e1, e2]):
                assert tc_exp(e1, env) == bool
                assert tc_exp(e2, env) == bool
                return bool
            case Prim("eq", [e1, e2]):
                assert tc_exp(e1, env) == tc_exp(e2, env)
                return bool
            case Prim("gt", [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return bool
            case Prim("gte", [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return bool
            case Prim("lt", [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return bool
            case Prim("lte", [e1, e2]):
                assert tc_exp(e1, env) == int
                assert tc_exp(e2, env) == int
                return bool

    def tc_stmt(s: Stmt, env: TEnv):
        match s:
            case Assign(x, e):
                if x in env:
                    assert env[x] == tc_exp(e, env)
                else:
                    env[x] = tc_exp(e, env)
            case Print(e):
                tc_exp(e, env)
            case If(e1, s1, s2):
                assert tc_exp(e1, env) == bool
                for stmt in s1:
                    tc_stmt(stmt, env)
                for stmt in s2:
                    tc_stmt(stmt, env)

    def tc_stmts(stmts: List[Stmt]):
        env = {}
        for stmt in stmts:
            tc_stmt(stmt, env)

    tc_stmts(program.stmts)

    return program


##################################################
# remove-complex-opera*
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Expr  ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts)
# Stmts ::= List[Stmt]
# LVar  ::= Program(Stmts)

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lif program
    :return: An Lif program with atomic operator arguments.
    """

    def rco_exp(e: Expr, bindings: Dict[str, Expr]) -> Expr:
        match e:
            case Constant(n):
                return Constant(n)
            case Var(x):
                return Var(x)
            case Prim(op, args):
                # new_args = [rco_exp(a) for a in args]
                new_args = []
                for a in args:
                    new_args.append(rco_exp(a, bindings))
                    # recursive call to rco_exp should make the argument atomic
                tmp = gensym('tmp')
                # bind tmp to prim(op, new_args)
                bindings[tmp] = Prim(op, new_args)
                return Var(tmp)

    def rco_stmt(s: Stmt, bindings: Dict[str, Expr]) -> Stmt:
        match s:
            case Assign(x, e):
                return Assign(x, rco_exp(e, bindings))
            case Print(e):
                return Print(rco_exp(e, bindings))
            case If(condition, then_stmts, else_stmts):
                return If(rco_exp(condition, bindings),
                          rco_stmts(then_stmts),
                          rco_stmts(else_stmts))
            case _:
                raise Exception('rco_stmt', s)


    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
        new_stmts = []
        for stmt in stmts:
            bindings = {}
            new_stmt = rco_stmt(stmt, bindings)
            for b in bindings:
                # print(b, bindings[b])
                new_stmts.append(Assign(b, bindings[b]))
            new_stmts.append(new_stmt)
        return new_stmts

    return Program(rco_stmts(prog.stmts))


##################################################
# explicate-control
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Atm   ::= Var(x) | Constant(n)
# Expr  ::= Atm | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts)
# Stmts ::= List[Stmt]
# LVar  ::= Program(Stmts)

def explicate_control(prog: Program) -> cif.CProgram:
    """
    Transforms an Lif Expression into a Cif program.
    :param prog: An Lif Expression
    :return: A Cif Program
    """
    #pass should have a global basic_blocks: Dict[str, List[cif.Stmt]]
    basic_blocks: Dict[str, List[cif.Stmt]] = {}

    #pass should have a create_block gunction that adds a new block to basic_blocks with a unique name (using gensym)
    def create_block(stmts: List[cif.Stmt]) -> str:
        new_label = gensym('label')
        basic_blocks[new_label] = stmts
        return new_label

    # - `ec_atm`
    # - Constants => cif.Constants
    # - Var => cif.Var

    def ec_atm(e: Expr) -> cif.Atm:
        pass
    # - `ec_expr` compiles an expression into a Cin expression
    # - Prim(op, args) => cif.Prim(op, new_args)
    # - else call ec_atm

    def ec_expr(e: Expr) -> cif.Expr:
        pass

    # - `ec_stmt` takes a statement and a continuation and returns a list of Cif statements
    # - Assign(x,e) => [cif.Assign(x, ec_expr(e))] + cont
    # - Print(e) => [cif.Print(ec_expr(e))] + cont
    # - If (condition, then_stmts, else_stmts) =>
    # - cond_label = create block for cont
    # - then_label = create block for ec_stmts(then_stmts, [cif.Goto(cond_label)])
    # - else_label = create block for ec_stmts(else_stmts, [cif.Goto(cond_label)])
    # - return[cif(ec_expr(condition), cif.Goto(then_label), cif.Goto(else_label)]

    def ec_stmt(s: Stmt, cont: List[cif.Stmt]) -> List[cif.Stmt]:
        match s:
            case Assign(x, e):
                new_stmt: List[cif.Stmt] = [cif.Assign(x, ec_expr(e))]
                return new_stmt + cont
            case Print(e):
                pass


    # - `ec_stmts` takes a list of statements and a continuation, returns a list Cif statements
    # - process list of statments in reverse
    # - update current continuation by calling ec_stmt on each stmt and setting the continuation to whatever comes back

    def ec_stmts(stmts: List[Stmt], cont: List[cif.Stmt]) -> List[cif.Stmt]:
        for s in reversed(stmts):
            cont = ec_stmt(s, cont)
        return cont

    # - main body of the pass
    # - start with continuation [cif.Return(0)]
    # - call ec_stmts on statements of the program
    # - set basic_blocks['start'] to the result
    # TODO: fill this in

    return cif.CProgram(basic_blocks)


##################################################
# select-instructions
##################################################
# op    ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Atm   ::= Var(x) | Constant(n)
# Expr  ::= Atm | Prim(op, List[Expr])
# Stmt  ::= Assign(x, Expr) | Print(Expr)
#        | If(Expr, Goto(label), Goto(label)) | Goto(label) | Return(Expr)
# Stmts ::= List[Stmt]
# Cif   ::= CProgram(Dict[label, Stmts])

def select_instructions(prog: cif.CProgram) -> x86.X86Program:
    """
    Transforms a Lif program into a pseudo-x86 assembly program.
    :param prog: a Lif program
    :return: a pseudo-x86 program
    """

    pass


##################################################
# allocate-registers
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]

def allocate_registers(program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    pass


##################################################
# patch-instructions
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Deref(r, offset)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

def patch_instructions(program: x86.X86Program) -> x86.X86Program:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    pass


##################################################
# prelude-and-conclusion
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Deref(r, offset)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

def prelude_and_conclusion(program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    pass


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86
}


def run_compiler(s, logging=False):
    def print_prog(current_program):
        print('Concrete syntax:')
        if isinstance(current_program, x86.X86Program):
            print(x86.print_x86(current_program))
        elif isinstance(current_program, Program):
            print(print_program(current_program))
        elif isinstance(current_program, cif.CProgram):
            print(cif.print_program(current_program))

        print()
        print('Abstract syntax:')
        print(print_ast(current_program))

    current_program = parse(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print_prog(current_program)

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print_prog(current_program)

    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())

