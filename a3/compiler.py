from collections import defaultdict

from typing import List, Set, Dict, Tuple, DefaultDict
import sys
import itertools
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86
import constants
from interference_graph import InterferenceGraph

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
# remove-complex-opera*
##################################################

# Same as compiler 2
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
                # print(b, bindings[b])
                new_stmts.append(Assign(b, bindings[b]))
            new_stmts.append(new_stmt)
        return new_stmts

    return Program(rco_stmts(prog.stmts))

# Same as compiler 2
##################################################
# select-instructions
##################################################

# Output language: pseudo-x86
# Arg ::= Immediate(n) | Var(x) | Reg(str)
# instr_name ::= "movq" | "addq"
# Instr ::= NamedInstr(instr_name, [Arg]) | Callq(str) | Retq()
# X86 ::= X86Program(Dict[str, [Instr]])

# Same as compiler 2
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
            # INSTRUCTOR SOLUTION
            # case _:
            # Exception

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

    def si_stmts(stmts: List[Stmt]) -> List[x86.Instr]:
        instrs = []
        for stmt in stmts:
            i = si_stmt(stmt)
            instrs.extend(i)
        return instrs

    return x86.X86Program({'main': si_stmts(prog.stmts)})


##################################################
# allocate-registers
##################################################

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]

# Input and Output language: pseudo-x86
# Arg ::= Immediate(n) | Var(x) | Reg(str)
# instr_name ::= "movq" | "addq"
# Instr ::= NamedInstr(instr_name, [Arg]) | Callq(str) | Retq()
# X86 ::= X86Program(Dict[str, [Instr]])


# Only different pass from compiler here
def allocate_registers(program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    # --------------------------------------------------
    # utilities
    # --------------------------------------------------

    def vars_of(a: x86.Arg) -> Set[x86.Var]:
        match a:
            case x86.Var(x):
                return {x86.Var(x)}
            case _:
                return set()

    # Ctrl-H to get class hierarchy
    def reads_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('addq', [a1, a2]):
                # addq reads both args so return the set of vars in a1 and a2
                return vars_of(a1).union(vars_of(a2))
            case x86.NamedInstr('movq', [a1, a2]):
                # movq reads a1
                return vars_of(a1)
            # The other cases are callq and retq, neither of which have args
            case _:
                return set()

    def writes_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('addq', [a1, a2]):
                return vars_of(a2)
            case x86.NamedInstr('movq', [a1, a2]):
                return vars_of(a2)
            # The other cases are callq and retq, neither of which have args
            case _:
                return set()

    # --------------------------------------------------
    # liveness analysis
    # --------------------------------------------------

    def ul_instr(i: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        return live_after.difference(writes_of(i)).union(reads_of(i))

    def ul_block(instrs: List[x86.Instr]) -> List[Set[x86.Var]]:
        live_after_sets = []
        current_live_after = set()
        for i in reversed(instrs):
            live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after)
        return list(reversed(live_after_sets))

    # --------------------------------------------------
    # interference graph
    # --------------------------------------------------
    def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        pass

    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        pass

    # --------------------------------------------------
    # graph coloring
    # --------------------------------------------------
    def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:
        pass

    # --------------------------------------------------
    # assigning homes
    # --------------------------------------------------

    # --------------------------------------------------
    # main body of the pass
    # --------------------------------------------------

    # Step 1: Perform liveness analysis
    blocks = program.blocks
    # TODO: run the liveness analysis
    live_after_sets = None # call ul_block
    log_ast('live-after sets', live_after_sets) # This will print out live-after sets

    # Step 2: Build the interference graph
    interference_graph = InterferenceGraph()

    # TODO: build the interference graph

    log_ast('interference graph', interference_graph)

    # Step 3: Color the graph
    coloring = None

    # TODO: color the interference graph

    log('coloring', coloring)

    # Defines the set of registers to use
    available_registers = constants.caller_saved_registers + constants.callee_saved_registers

    # Step 4: map variables to homes
    color_map = {}
    stack_locations_used = 0

    # Step 4.1: Map colors to locations (the "color map")
    # TODO: step 4.1

    # Step 4.2: Compose the "coloring" with the "color map" to get "homes"
    # TODO: step 4.2
    log('homes', homes)

    # Step 5: replace variables with their homes
    # TODO: step 5
    pass


##################################################
# patch-instructions
##################################################
# Same as compiler 2
def patch_instructions(program: x86.X86Program) -> x86.X86Program:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    def pi_instr(i: x86.Instr) -> List[x86.Instr]:
        new_instrs = []
        match i:
            case x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                new_instrs.append(x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Reg('rax')]))
                new_instrs.append(x86.NamedInstr('movq', [x86.Reg('rax'), x86.Deref(r2, o2)]))
            case x86.NamedInstr('addq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                new_instrs.append(x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Reg('rax')]))
                new_instrs.append(x86.NamedInstr('addq', [x86.Reg('rax'), x86.Deref(r2, o2)]))
            # Add exception here
            case _r:
                new_instrs.append(_r)
        return new_instrs

    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instrs = []
        for i in instrs:
            new_instrs.extend(pi_instr(i))
        return new_instrs

    blocks = program.blocks
    new_blocks = {}

    for item in blocks:
        new_blocks[item] = pi_block(program.blocks[item])

    return x86.X86Program(new_blocks, stack_space=program.stack_space)


##################################################
# prelude-and-conclusion
##################################################
# Same as compiler 2
def prelude_and_conclusion(program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    def pc_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instr = []
        new_instr.extend([x86.NamedInstr('pushq', [x86.Reg("rbp")]),
                         x86.NamedInstr('movq', [x86.Reg("rsp"), x86.Reg("rbp")]),
                         x86.NamedInstr('subq', [x86.Immediate(program.stack_space), x86.Reg("rsp")])])
        new_instr.extend(instrs)
        new_instr.extend([x86.NamedInstr('addq', [x86.Immediate(program.stack_space), x86.Reg("rsp")]),
                          x86.NamedInstr('popq', [x86.Reg('rbp')]),
                          x86.Retq()])
        return new_instr

    blocks = program.blocks
    new_blocks = {}
    for item in blocks:
        new_blocks[item] = pc_block(program.blocks[item])

    return x86.X86Program(new_blocks, stack_space=program.stack_space)

    pass


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'remove complex opera*': rco,
    'select instructions': select_instructions,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86
}


def run_compiler(s, logging=False):
    global global_logging
    global_logging = logging

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
