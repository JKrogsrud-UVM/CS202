from typing import List, Set, Dict, Tuple
import sys
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86

# Input Language: LVar
# op ::= "add"
# Expr ::= Var(x) | Constant(n) | Prim(op, [Expr])
# Stmt ::= Assign(x, Expr) | Print(Expr)
# LVar ::= Program([Stmt])

gensym_num = 0

"""
Notes: Removes complex operands basically removes nested expressions
select_instructions: This pass trabslates the python to x86 (sort of, it will have variables)
assign_homes: removes variables
"""

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
# remove-complex-opera*
##################################################
"""
In words: (See notebook)

Our structure will follow the stucture of the grammar:

- rco_exp compiles an expression
- rco_stmt compiles a statement
- rco_stmts compiles a list of statements

rco_stmt compiles a statement
    - Assign(x,e): call rco_exp on e
    - Print(e): call rco_exp on e
    - Challenge: what about bindings?
- rco_stmts compiles a list of statements
    - For each stmt
        - call rco stmt on each stmt
        - turn the bindings that were created into assignment statements

"""

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lvar program
    :return: An Lvar program with atomic operator arguments.
    """

    # This should always return an atomic expression
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

    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
        new_stmts = []
        for stmt in stmts:
            bindings = {}
            new_stmt = rco_stmt(stmt, bindings)
            for b in bindings:
                print(b, bindings[b])
                new_stmts.append(Assign(b, bindings[b]))
            new_stmts.append(new_stmt)
        return new_stmts

    return Program(rco_stmts(prog.stmts))


##################################################
# select-instructions
##################################################

# Output language: pseudo-x86
# ATM ::= Immediate(n) | Var(x) | Reg(str)
# instr_name ::= "movq" | "addq"
# Instr ::= NamedInstr(instr_name, [Atm]) | Callq(str) | Retq()
# X86 ::= X86Program(Dict[str, [Instr]])

def select_instructions(prog: Program) -> x86.X86Program:
    """
    Transforms a Lvar program into a pseudo-x86 assembly program.
    :param prog: a Lvar program
    :return: a pseudo-x86 program
    """

    def si_atm(atm: Expr) -> x86.Arg:
        match atm:
            case Var(x):
                return x86.Var(x)
            case Constant(n):
                return x86.Immediate(n)

    def si_stmt(stmt: Stmt) -> List[x86.Instr]:

        match stmt:
            case Assign(x, Prim('add', [atm1, atm2])):
                x86atm1 = si_atm(atm1)
                x86atm2 = si_atm(atm2)
                return [x86.NamedInstr("movq", [x86atm1, x86.Reg("rax")]),
                        x86.NamedInstr("addq", [x86atm2, x86.Reg("rax")]),
                        x86.NamedInstr("movq", [x86.Reg("rax"), x86.Var(x)])]
            case Assign(x, atm1):
                x86atm1 = si_atm(atm1)
                return [x86.NamedInstr("movq", [x86atm1, x86.Var(x)])]
            case Print(atm):
                x86atm = si_atm(atm)
                return [x86.NamedInstr("movq", [x86atm, x86.Reg("rdi")]),
                        x86.Callq("print_int")]

    def si_stmts(stmts: List[Stmt]) ->List[x86.Instr]:
        instrs = []
        for stmt in stmts:
            i = si_stmt(stmt)
            instrs.extend(i)
        return instrs

    return x86.X86Program({'main': si_stmts(prog.stmts)})


##################################################
# assign-homes
##################################################

def assign_homes(program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates a stack location for each
    variable in the program.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the amount of stack space used
    """

    homes = {}
    def ah_args(a: x86.Arg):
        match a:
            case x86.Reg(r):
                return x86.Reg(r)
            case x86.Immediate(i):
                return x86.Immediate(i)
            case x86.Var(v):
                if v in homes:
                    return x86.Reg(homes[v])
                else:
                    offset = -8*(len(homes)+1)
                    homes[v] = x86.Deref("rbp", offset)
                return homes[v]


    def ah_instr(instr: x86.Instr):
        match instr:
            case x86.NamedInstr(op, args):
                return x86.NamedInstr(op, [ah_args(a) for a in args])
            case r:
                return r

    def ah_block(instr: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instr]


    for block in program:
        program[prog] = ah_block(prog)
    return x86.X86Program({})


##################################################
# patch-instructions
##################################################

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
    'remove complex opera*': rco,
    'select instructions': select_instructions,
    'assign homes': assign_homes,
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
