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
# op     ::= "add" | "sub" | "not" | "mult" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
# Stmts  ::= List[Stmt]
# LWhile ::= Program(Stmts)

TEnv = Dict[str, type]


def typecheck(program: Program) -> Program:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param program: The Lif program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        'add': [int, int],
        'sub': [int, int],
        'mult': [int, int],
        'not': [bool],
        'or': [bool, bool],
        'and': [bool, bool],
        'gt': [int, int],
        'gte': [int, int],
        'lt': [int, int],
        'lte': [int, int],
    }

    prim_output_types = {
        'add': int,
        'sub': int,
        'mult': int,
        'not': bool,
        'or': bool,
        'and': bool,
        'gt': bool,
        'gte': bool,
        'lt': bool,
        'lte': bool,
    }

    def tc_exp(e: Expr, env: TEnv) -> type:
        match e:
            case Var(x):
                return env[x]
            case Constant(i):
                if isinstance(i, bool):
                    return bool
                elif isinstance(i, int):
                    return int
                else:
                    raise Exception('tc_exp', e)
            case Prim('eq', [e1, e2]):
                assert tc_exp(e1, env) == tc_exp(e2, env)
                return bool
            case Prim(op, args):
                arg_types = [tc_exp(a, env) for a in args]
                assert arg_types == prim_arg_types[op]
                return prim_output_types[op]
            case _:
                raise Exception('tc_exp', e)

    def tc_stmt(s: Stmt, env: TEnv):
        match s:
            case If(condition, then_stmts, else_stmts):
                assert tc_exp(condition, env) == bool

                for s in then_stmts:
                    tc_stmt(s, env)
                for s in else_stmts:
                    tc_stmt(s, env)
            case Print(e):
                tc_exp(e, env)
            case Assign(x, e):
                t_e = tc_exp(e, env)
                if x in env:
                    assert t_e == env[x]
                else:
                    env[x] = t_e
            case _:
                raise Exception('tc_stmt', s)

    def tc_stmts(stmts: List[Stmt], env: TEnv):
        for s in stmts:
            tc_stmt(s, env)

    env = {}
    tc_stmts(program.stmts, env)
    return program


##################################################
# remove-complex-opera*
##################################################
# op     ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
# Stmts  ::= List[Stmt]
# LWhile ::= Program(Stmts)

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lif program
    :return: An Lif program with atomic operator arguments.
    """

    pass


##################################################
# explicate-control
##################################################
# op     ::= "add" | "sub" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
# Atm    ::= Var(x) | Constant(n)
# Expr   ::= Atm | Prim(op, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Begin(Stmts, Expr), Stmts)
# Stmts  ::= List[Stmt]
# LWhile ::= Program(Stmts)

def explicate_control(prog: Program) -> cif.CProgram:
    """
    Transforms an Lif Expression into a Cif program.
    :param prog: An Lif Expression
    :return: A Cif Program
    """

    pass


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

