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
            case Prim("or", [e1, e2]):
                assert tc_exp(e1, env) == bool
                assert tc_exp(e2, env) == bool
                return bool
            case Prim("and", [e1, e2]):
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
            case Prim("not", [e1]):
                assert tc_exp(e1, env) == bool
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

    # TODO: Modify this to allow for some conditions to be non-atomic (specifically some of our if statements)

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

# RCO outputs: Expr: Var(x) | Constant(n) | Prim(op, List[Expr])
def explicate_control(prog: Program) -> cif.CProgram:
    """
    Transforms an Lif Expression into a Cif program.
    :param prog: An Lif Expression
    :return: A Cif Program
    """
    #pass should have a global basic_blocks: Dict[str, List[cif.Stmt]]
    basic_blocks: Dict[str, List[cif.Stmt]] = {}

    def create_block(stmts: List[cif.Stmt]) -> str:
        new_label = gensym('label')
        basic_blocks[new_label] = stmts
        return new_label

    # Graduate Stuff
    # TODO: explicate_pred
    """
    Input:
        1) The condition expression
        2) The generated statements for the then branch
        3) The generated statements for the else branch
        4) *Left out as it's Global* The dictionary of basic blocks
    """
    def ec_pred(cnd, thn, els) -> List[cif.Stmt]:
        """
        From book:

        match cnd:
            case Compare(left [op] right):
                goto_thn = create_block(thn, basic_blocks)
                goto_els = create_block(els, basic_blocks)
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case Unary( Not, op):
                ...
            case IfExp(test, body, orelse):
                ...
            case Begin(body, result):
                ...
            case _:
                return [If(Compare(cnd [Eq()] [Constant(False)]),
                        create_block(els, basic_blocks),
                        create_block(thn, basic_blocks))]
        """

        pass

    # - `ec_atm`
    # - Constants => cif.Constants
    # - Var => cif.Var
    def ec_atm(e: Expr) -> cif.Atm:
        match e:
            case Constant(c):
                return cif.Constant(c)
            case Var(x):
                return cif.Var(x)

    # - `ec_expr` compiles an expression into a Cin expression
    # - Prim(op, args) => cif.Prim(op, new_args)
    # - else call ec_atm

    def ec_expr(e: Expr) -> cif.Expr:
        match e:
            case Prim(op, args):
                return cif.Prim(op, [ec_atm(arg) for arg in args])
            case _:
                return ec_atm(e)

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
                new_stmt: List[cif.Stmt] = [cif.Print(ec_expr(e))]
                return new_stmt + cont
            case If(condition, then_stmts, else_stmts):
                cont_label = gensym('label')
                basic_blocks[cont_label] = cont
                then_label = gensym('label')
                basic_blocks[then_label] = ec_stmts(then_stmts, [cif.Goto(cont_label)])
                else_label = gensym('label')
                basic_blocks[else_label] = ec_stmts(else_stmts, [cif.Goto(cont_label)])
                return [cif.If(ec_expr(condition), cif.Goto(then_label), cif.Goto(else_label))]


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

    cont = [cif.Return(cif.Constant(0))]
    basic_blocks['start'] = ec_stmts(prog.stmts, cont)
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

    def si_atm(atm: cif.Expr) -> x86.Arg:
        match atm:
            case cif.Var(x):
                return x86.Var(x)
            case cif.Constant(n):       # slightly different because booleans!
                return x86.Immediate(int(n))   # converts our booleans
            case _:
                raise Exception('si_atm', atm)

    #  "add" | "sub" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"

    binary_operators: Dict[str: str] = {
        'add': 'addq',
        'sub': 'subq',
        'or': 'orq',
        'and': 'andq'
    }

    comparison_codes: Dict[str, str] = {
        "eq": "e",
        "gt": "g",
        "gte": "ge",
        "lt": "l",
        "lte": "le"
    }

    def si_stmt(stmt: cif.Stmt) -> List[x86.Instr]:
        match stmt:
            case cif.Assign(x, cif.Prim(op, [atm1, atm2])):
                x86atm1 = si_atm(atm1)
                x86atm2 = si_atm(atm2)
                if op in binary_operators:
                    return [x86.NamedInstr("movq", [x86atm1, x86.Reg("rax")]),
                            x86.NamedInstr(binary_operators[op], [x86atm2, x86.Reg("rax")]),
                            x86.NamedInstr("movq", [x86.Reg("rax"), x86.Var(x)])]
                elif op in comparison_codes:
                    return [x86.NamedInstr("cmpq", [x86atm2, x86atm1]),
                            x86.Set(comparison_codes[op], x86.ByteReg("al")),
                            x86.NamedInstr("movzbq", [x86.ByteReg("al"), x86.Var(x)])]
            case cif.Assign(x, cif.Prim('not', [atm])):
                x86atm = si_atm(atm)
                return [x86.NamedInstr("movq", [x86atm, x86.Var(x)]),
                        x86.NamedInstr("xorq", [x86.Immediate(1), x86.Var(x)])]
            case cif.Assign(x, atm):
                x86atm1 = si_atm(atm)
                return [x86.NamedInstr("movq", [x86atm1, x86.Var(x)])]
            case cif.Print(atm):
                x86atm = si_atm(atm)
                return [x86.NamedInstr("movq", [x86atm, x86.Reg("rdi")]),
                        x86.Callq("print_int")]
            case cif.If(cif.Var(x), cif.Goto(l1), cif.Goto(l2)):
                return [x86.NamedInstr("cmpq", [x86.Var(x), x86.Immediate(1)]),
                        x86.JmpIf("e", l1),
                        x86.Jmp(l2)]
            case cif.Goto(l):
                return [x86.Jmp(l)]
            case cif.Return(cif.Constant(c)):
                return [x86.NamedInstr("movq", [x86.Immediate(c), x86.Reg("rax")]),
                        x86.Jmp('conclusion')]
            case _:
                raise Exception('si_stmt', stmt)

    def si_stmts(stmts: List[cif.Stmt]) -> List[x86.Instr]:
        instrs = []
        for stmt in stmts:
            i = si_stmt(stmt)
            instrs.extend(i)
        return instrs

    new_prog: Dict[str: List[x86.Instr]] = {}

    for label in prog.blocks:
        new_prog[label] = si_stmts(prog.blocks[label])

    return x86.X86Program(new_prog)

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

    binary_operators: Dict[str: str] = {
        'add': 'addq',
        'sub': 'subq',
        'or': 'orq',
        'and': 'andq'
    }

    comparison_codes: Dict[str, str] = {
        "eq": "e",
        "gt": "g",
        "gte": "ge",
        "lt": "l",
        "lte": "le"
    }

    all_vars: Set[x86.Var] = set()

    live_after_sets: Dict[str: List[Set[x86.Var]]] = {}
    live_before_sets: Dict[str: Set[x86.Var]] = {}
    live_before_sets['conclusion'] = set()

    # --------------------------------------------------
    # utilities
    # --------------------------------------------------
    def vars_arg(a: x86.Arg) -> Set[x86.Var]:
        match a:
            case x86.Immediate(i):
                return set()
            case x86.Reg(r):
                return set()
            case x86.Var(x):
                all_vars.add(x86.Var(x))
                return {x86.Var(x)}
            case _:
                raise Exception('ul_arg', a)

    # Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
    #         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)

    def reads_of(i: x86.Instr, label: str) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr('movq', [e1, e2]):
                return vars_arg(e1)
            case x86.NamedInstr('addq', [e1, e2]):
                return vars_arg(e1).union(vars_arg(e2))
            case x86.NamedInstr('cmpq', [a1, a2]):
                return vars_arg(a1).union(vars_arg(a2))
            case x86.Jmp(l1):
                if l1 in live_before_sets:
                    return live_before_sets[l1]
                else:
                    ul_block(l1)
                    return live_before_sets[l1]
            case x86.JmpIf(cc, l1):
                if l1 in live_before_sets:
                    return live_before_sets[l1].union(live_before_sets[label])
                else:
                    ul_block(l1)
                    return live_before_sets[l1]
            case _:
                return set()

    # NamedInstr(op, List[Arg]) | Callq(label) | Retq()
    #                             | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
    #  op: 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
    def writes_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.NamedInstr(op, [e1, e2]):
                if op in binary_operators:
                    return vars_arg(e2)
                if op == 'movq':
                    return vars_arg(e2)
                if op == 'movzbq':
                    return vars_arg(e2)
                if op == 'xorq':
                    return vars_arg(e2)
                else:
                    return set()
            case _:
                return set()

    # --------------------------------------------------
    # liveness analysis
    # --------------------------------------------------
    # Computes live-after set
    def ul_instr(i: x86.Instr, live_after: Set[x86.Var], label: str) -> Set[x86.Var]:
        # live after set here is the live-before of previous instruction
        live_before = (live_after.difference(writes_of(i))).union(reads_of(i, label))
        return live_before

    def ul_block(label: str):
        current_live_after = set()
        local_live_after_sets = []

        instructions = program.blocks

        for i in reversed(instructions[label]):
            local_live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after, label)

        live_before_sets[label] = current_live_after
        live_after_sets[label] = list(reversed(local_live_after_sets))

    # def ul_block(label: str):
    #
    #     instructions = program.blocks[label]
    #     live_before = set()
    #
    #     if label not in live_after_sets:
    #         live_after_sets[label] = []
    #
    #     live_after_sets[label].append(live_before)
    #     live_before_sets[label] = live_before
    #
    #     for i in reversed(instructions):
    #         live_after_of_i = live_after_sets[label][-1]  # construct the live_before
    #         live_before_of_i = ul_instr(i, live_after_of_i, label)  # (live_after_of_i - Writes) union reads
    #         live_after_sets[label].append(live_before_of_i)  # add it to the list


    # --------------------------------------------------
    # interference graph
    # --------------------------------------------------
    def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        for v1 in writes_of(e):
            for v2 in live_after:
                graph.add_edge(v1, v2)

    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        for instr, live_after in zip(instrs, live_afters):
            bi_instr(instr, live_after, graph)

    # --------------------------------------------------
    # graph coloring
    # --------------------------------------------------
    def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:
        coloring: Coloring = {}

        to_color = local_vars.copy()

        # Saturation sets start out empty
        saturation_sets = {x: set() for x in local_vars}

        # Loop until we are finished coloring
        while to_color:
            # Find the variable x with the largest saturation set
            x = max(to_color, key=lambda x: len(saturation_sets[x]))

            # Remove x from the variables to color
            to_color.remove(x)

            # Find the smallest color not in x's saturation set
            x_color = next(i for i in itertools.count() if i not in saturation_sets[x])

            # Assign x's color
            coloring[x] = x_color

            # Add x's color to the saturation sets of its neighbors
            for y in interference_graph.neighbors(x):
                saturation_sets[y].add(x_color)

        return coloring

    # --------------------------------------------------
    # assigning homes
    # --------------------------------------------------
    def align(num_bytes: int) -> int:
        if num_bytes % 16 == 0:
            return num_bytes
        else:
            return num_bytes + (16 - (num_bytes % 16))

    homes: Dict[str, x86.Arg] = {}

    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(i):
                return a
            case x86.Reg(r):
                return a
            case x86.ByteReg(r):
                return a
            case x86.Var(x):
                return homes[a]
            case _:
                raise Exception('ah_arg', a)

    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.NamedInstr(i, args):
                return x86.NamedInstr(i, [ah_arg(a) for a in args])
            case x86.Set(cc, arg):
                return x86.Set(cc, ah_arg(arg))
            case _:
                if isinstance(e, (x86.Callq, x86.Retq, x86.Jmp, x86.JmpIf)):
                    return e
                else:
                    raise Exception('ah_instr', e)

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]

    # --------------------------------------------------
    # main body of the pass
    # --------------------------------------------------

    # Step 1: Perform liveness analysis
    blocks = program.blocks
    ul_block('start')
    log_ast('live-after sets', live_after_sets)

    # Step 2: Build the interference graph
    interference_graph = InterferenceGraph()

    for label in blocks.keys():
        bi_block(blocks[label], live_after_sets[label], interference_graph)

    log_ast('interference graph', interference_graph)

    # Step 3: Color the graph
    coloring = color_graph(all_vars, interference_graph)
    colors_used = set(coloring.values())
    log('coloring', coloring)

    # Defines the set of registers to use
    available_registers = constants.caller_saved_registers + constants.callee_saved_registers

    # Step 4: map variables to homes
    color_map = {}
    stack_locations_used = 0

    # Step 4.1: Map colors to locations (the "color map")
    for color in colors_used:
        if available_registers != []:
            r = available_registers.pop()
            color_map[color] = x86.Reg(r)
        else:
            offset = stack_locations_used + 1
            color_map[color] = x86.Deref('rbp', -(offset * 8))
            stack_locations_used += 1

    # Step 4.2: Compose the "coloring" with the "color map" to get "homes"
    for v in all_vars:
        homes[v] = color_map[coloring[v]]
    log('homes', homes)

    # Step 5: replace variables with their homes
    blocks = program.blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}

    return x86.X86Program(new_blocks, stack_space=align(8 * stack_locations_used))

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

    def pi_instr(i: x86.Instr) -> List[x86.Instr]:
        new_instrs = []
        match i:
            case x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                new_instrs.append(x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Reg('rax')]))
                new_instrs.append(x86.NamedInstr('movq', [x86.Reg('rax'), x86.Deref(r2, o2)]))
            case x86.NamedInstr('addq', [x86.Deref(r1, o1), x86.Deref(r2, o2)]):
                new_instrs.append(x86.NamedInstr('movq', [x86.Deref(r1, o1), x86.Reg('rax')]))
                new_instrs.append(x86.NamedInstr('addq', [x86.Reg('rax'), x86.Deref(r2, o2)]))
            case x86.NamedInstr('cmpq', [a1, x86.Immediate(i)]):
                new_instrs.append(x86.NamedInstr('movq', [x86.Immediate(i), x86.Reg('rax')]))
                new_instrs.append(x86.NamedInstr('cmpq', [a1, x86.Reg('rax')]))
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

    # prelude now should have a jmp start
    # conclusion doesn't change
    # program.blocks['main'] = prelude
    # program.blocks['conclusion'] = conclusion
    # return x86.X86Program(program.blocks, stack_space = program.stack_space)

    prelude = [x86.NamedInstr('pushq', [x86.Reg('rbp')]),
               x86.NamedInstr('movq', [x86.Reg('rsp'), x86.Reg('rbp')]),
               x86.NamedInstr('subq', [x86.Immediate(program.stack_space), x86.Reg('rsp')]),
               x86.Jmp('start')]

    conclusion = [x86.NamedInstr('addq', [x86.Immediate(program.stack_space),
                                          x86.Reg('rsp')]),
                  x86.NamedInstr('popq', [x86.Reg('rbp')]),
                  x86.Retq()]

    program.blocks['main'] = prelude
    program.blocks['conclusion'] = conclusion

    return x86.X86Program(program.blocks, stack_space=program.stack_space)

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

