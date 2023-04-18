from typing import Set, Dict, Tuple
from dataclasses import dataclass
import sys
import traceback

from cs202_support.python import *
import cs202_support.x86 as x86
import constants
import cfun
import print_x86defs
from interference_graph import InterferenceGraph

comparisons = ['eq', 'gt', 'gte', 'lt', 'lte']
gensym_num = 0
global_logging = False

global_values = ['free_ptr', 'fromspace_end']

tuple_var_types = {}
function_names = set()

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
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr]) | Begin(Stmts, Expr)
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

@dataclass
class Callable:
    args: List[type]
    output_type: type


TEnv = Dict[str, Callable | Tuple | type]


def typecheck(program: Program) -> Program:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param program: The Ltup program to typecheck
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
            case Call(Var(func), args):
                # args is List[Expr]
                """
                1. Assume we have already type-checked the definition of f
                2. typecheck f; it should have the type Callable([t1, ... , tk], t) --- (assertion)
                3. Typecheck a1, ... , ak and ensure they have the same types as the 
                   arguments in the function def (t1, .. tk) --- (lots of assertions)
                4. Return the type t
                """
                # Call(Expr, List[Expr])
                # How to typecheck part 2 here?
                tc_exp(Var(func), env)
                func_callable = env[func]
                for arg_no in range(len(args)):
                    assert tc_exp(args[arg_no], env) == func_callable.args[arg_no]
                return env[func].output_type

            case Var(x):
                if x in global_values:
                    return int
                else:
                    return env[x]
            case Constant(i):
                if isinstance(i, bool):
                    return bool
                elif isinstance(i, int):
                    return int
                else:
                    raise Exception('tc_exp', e)
            case Prim('tuple', args):
                arg_types = [tc_exp(a, env) for a in args]
                t = tuple(arg_types)
                return t
            case Prim('subscript', [e1, Constant(i)]):
                t = tc_exp(e1, env)
                assert isinstance(t, tuple)
                return t[i]
            case Prim('eq', [e1, e2]):
                assert tc_exp(e1, env) == tc_exp(e2, env)
                return bool
            case Prim(op, args):
                arg_types = [tc_exp(a, env) for a in args]
                assert arg_types == prim_arg_types[op]
                return prim_output_types[op]
            case Begin(stmts, e):
                tc_stmts(stmts, env)
                return tc_exp(e, env)
            case _:
                raise Exception('tc_exp', e)

    def tc_stmt(s: Stmt, env: TEnv):
        match s:
            # FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
            case FunctionDef(name, params, body_stmts, return_type):

                # Make a list of types of the params for function signature
                param_types: List[type] = [tup[1] for tup in params]
                # Set the function name with Callable type in environment
                env[name] = Callable(param_types, return_type)

                # Copy env
                new_env = env.copy()

                # Add each param to new environment
                for param in params:
                    new_env[param[0]] = param[1]

                new_env['ret_val'] = return_type
                tc_stmts(body_stmts, new_env)

                function_names.add(name)

            # Can be assumed will happen after function def?
            case Return(e):
                assert tc_exp(e, env) == env['ret_val']

            case While(condition, body_stmts):
                assert tc_exp(condition, env) == bool
                tc_stmts(body_stmts, env)

            case If(condition, then_stmts, else_stmts):
                assert tc_exp(condition, env) == bool
                tc_stmts(then_stmts, env)
                tc_stmts(else_stmts, env)

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
    for x in env:
        if isinstance(env[x], tuple):
            tuple_var_types[x] = env[x]
    return program


##################################################
# remove-complex-opera*
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Ltup program
    :return: An Ltup program with atomic operator arguments.
    """

    def rco_stmt(stmt: Stmt, bindings: Dict[str, Expr]) -> Stmt:
        match stmt:
            case FunctionDef(name, params, body_stmts, return_type):
                return FunctionDef(name, params, rco_stmts(body_stmts), return_type)
            case Return(e):
                return Return(rco_exp(e, bindings))
            case Assign(x, e1):
                new_e1 = rco_exp(e1, bindings)
                return Assign(x, new_e1)
            case Print(e1):
                new_e1 = rco_exp(e1, bindings)
                return Print(new_e1)
            case While(condition, body_stmts):
                condition_bindings = {}
                condition_exp = rco_exp(condition, condition_bindings)
                condition_stmts = [Assign(x, e) for x, e in condition_bindings.items()]
                new_condition = Begin(condition_stmts, condition_exp)

                new_body_stmts = rco_stmts(body_stmts)
                return While(new_condition, new_body_stmts)

            case If(condition, then_stmts, else_stmts):
                new_condition = rco_exp(condition, bindings)
                new_then_stmts = rco_stmts(then_stmts)
                new_else_stmts = rco_stmts(else_stmts)

                return If(new_condition,
                          new_then_stmts,
                          new_else_stmts)
            case _:
                raise Exception('rco_stmt', stmt)

    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
        new_stmts = []

        for stmt in stmts:
            bindings = {}
            # (1) compile the statement
            new_stmt = rco_stmt(stmt, bindings)
            # (2) add the new bindings created by rco_exp
            new_stmts.extend([Assign(x, e) for x, e in bindings.items()])
            # (3) add the compiled statement itself
            new_stmts.append(new_stmt)

        return new_stmts

    def rco_exp(e: Expr, bindings: Dict[str, Expr]) -> Expr:
        match e:
            case Call(Var(func), params):

                new_params = [rco_exp(p, bindings) for p in params]
                func_var = rco_exp(Var(func), bindings)

                new_e = Call(func_var, new_params)
                new_v = gensym('tmp')
                bindings[new_v] = new_e

                return Var(new_v)

            case Var(x):

                # If x is a function make a tmp for it and return that
                if x in function_names:
                    tmp_x = gensym('tmp')
                    bindings[tmp_x] = Var(x)
                    return Var(tmp_x)

                return Var(x)

            case Constant(i):
                return Constant(i)

            case Prim(op, args):

                new_args = [rco_exp(e, bindings) for e in args]
                new_e = Prim(op, new_args)
                new_v = gensym('tmp')
                bindings[new_v] = new_e

                return Var(new_v)
            case _:
                raise Exception('rco_exp', e)

    return Program(rco_stmts(prog.stmts))


##################################################
# expose-allocation
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Begin(Stmts, Expr), Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def expose_alloc(prog: Program) -> Program:
    """
    Exposes allocations in an Ltup program. Replaces tuple(...) with explicit
    allocation.
    :param prog: An Ltup program
    :return: An Ltup program, without Tuple constructors
    """

    """
    ea_stmt:
        case FunctionDef:
            pass
    """

    def mk_tag(types: Tuple[type]) -> int:
        """
        Builds a vector tag. See section 5.2.2 in the textbook.
        :param types: A list of the types of the vector's elements.
        :return: A vector tag, as an integer.
        """
        pointer_mask = 0
        # for each type in the vector, encode it in the pointer mask
        for t in reversed(types):
            # shift the mask by 1 bit to make room for this type
            pointer_mask = pointer_mask << 1

            if isinstance(t, tuple):
                # if it's a vector type, the mask is 1
                pointer_mask = pointer_mask + 1
            else:
                # otherwise, the mask is 0 (do nothing)
                pass

        # shift the pointer mask by 6 bits to make room for the length field
        mask_and_len = pointer_mask << 6
        mask_and_len = mask_and_len + len(types) # add the length

        # shift the mask and length by 1 bit to make room for the forwarding bit
        tag = mask_and_len << 1
        tag = tag + 1

        return tag

    def ea_stmt(stmt: Stmt) -> List[Stmt]:
        match stmt:
            case If(cond, then_stmts, else_stmts):
                return [If(cond, ea_stmts(then_stmts), ea_stmts(else_stmts))]
            case While(Begin(s1, cond), s2):
                return [While(Begin(ea_stmts(s1), cond), ea_stmts(s2))]
            case Assign(x, Prim('tuple', args)):
                new_stmts = []
                num_bytes = 8 * (len(args) + 1)
                new_fp = gensym('tmp')
                lt_var = gensym('tmp')
                tag = mk_tag(tuple_var_types[x])
                new_stmts += [
                    Assign(new_fp, Prim('add', [Var('free_ptr'), Constant(num_bytes)])),
                    Assign(lt_var, Prim('lt', [Var(new_fp), Var('fromspace_end')])),
                    If(Var(lt_var),
                       [],
                       [Assign('_', Prim('collect', [Constant(num_bytes)]))]),
                    Assign(x, Prim('allocate', [Constant(num_bytes), Constant(tag)]))]

                # fill in the values of the tuple
                for i, a in enumerate(args):
                    new_stmts.append(Assign('_', Prim('tuple_set', [Var(x), Constant(i), a])))
                return new_stmts
            case FunctionDef(name, params, body_stmts, return_type):
                return [FunctionDef(name, params, ea_stmts(body_stmts), return_type)]
            case _:
                return [stmt]

    def ea_stmts(stmts: List[Stmt]) -> List[Stmt]:
        new_stmts = []
        for s in stmts:
            new_stmts.extend(ea_stmt(s))
        return new_stmts

    return Program(ea_stmts(prog.stmts))


##################################################
# explicate-control
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "subscript" | "allocate" | "collect" | "tuple_set"
# Atm    ::= Var(x) | Constant(n)
# Expr   ::= Atm | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Begin(Stmts, Expr), Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def explicate_control(prog: Program) -> cfun.CProgram:
    """
    Transforms an Lfun Expression into a Cfun program.
    :param prog: An Lfun Expression
    :return: A Cfun Program
    """

    # Note:
    # Cfun::= CProgram(List[CFunctionDef])
    # Output if very different

    # the basic blocks of the program
    basic_blocks: Dict[str, List[cfun.Stmt]] = {}
    functions: List[cfun.CFunctionDef] = []
    current_function = 'main'

    # FOLLOWING IS COPIED FROM PREVIOUS COMPILER: MIGHT NEED CHANGES
    basic_blocks: Dict[str, List[cfun.Stmt]] = {}

    # create a new basic block to hold some statements
    # generates a brand-new name for the block and returns it

    def create_block(stmts: List[cfun.Stmt]) -> str:
        label = gensym('label')
        basic_blocks[current_function + label] = stmts
        return current_function + label

    def explicate_atm(e: Expr) -> cfun.Atm:
        match e:
            case Var(x):
                return cfun.Var(x)
            case Constant(c):
                return cfun.Constant(c)
            case _:
                raise RuntimeError(e)

    def explicate_exp(e: Expr) -> cfun.Expr:
        match e:
            case Call(func, args):
                new_func = explicate_atm(func)
                new_args = [explicate_atm(a) for a in args]
                return cfun.Call(new_func, new_args)

            case Prim(op, args):
                new_args = [explicate_atm(a) for a in args]
                return cfun.Prim(op, new_args)
            case _:
                return explicate_atm(e)

    def ec_function(name: str, params: List[Tuple[str, type]],
                    body_stmts: List[Stmt], return_type: type):

        nonlocal basic_blocks  # defined in local context but not Global
        nonlocal current_function
        old_basic_blocks = basic_blocks
        old_current_function = current_function
        basic_blocks = {}
        current_function = name

        body_stmts_end = body_stmts[-1]

        # Check with Prof on this guy
        match body_stmts_end:
            case Return(e):
                new_cont = explicate_stmts(body_stmts, [])
            case _:
                new_cont = explicate_stmts(body_stmts, [cfun.Return(cfun.Constant(0))])
        basic_blocks[name + 'start'] = new_cont

        args = [p[0] for p in params]
        funcDef = cfun.CFunctionDef(name, args, basic_blocks)
        functions.append(funcDef)

        basic_blocks = old_basic_blocks
        current_function = old_current_function

    def explicate_stmt(stmt: Stmt, cont: List[cfun.Stmt]) -> List[cfun.Stmt]:
        match stmt:
            case Return(e):
                new_exp = explicate_atm(e)
                new_stmt: List[cfun.Stmt] = [cfun.Return(new_exp)]
                return new_stmt + cont
            case FunctionDef(name, params, body_stmts, return_type):
                ec_function(name, params, body_stmts, return_type)
                return cont
            case Assign(x, exp):
                new_exp = explicate_exp(exp)
                new_stmt: List[cfun.Stmt] = [cfun.Assign(x, new_exp)]
                return new_stmt + cont
            case Print(exp):
                new_exp = explicate_atm(exp)
                new_stmt: List[cfun.Stmt] = [cfun.Print(new_exp)]
                return new_stmt + cont
            case While(Begin(condition_stmts, condition_exp), body_stmts):
                cont_label = create_block(cont)
                test_label = gensym(current_function + 'loop_label')
                body_label = create_block(explicate_stmts(body_stmts, [cfun.Goto(test_label)]))
                test_stmts = [cfun.If(explicate_exp(condition_exp),
                                      cfun.Goto(body_label),
                                      cfun.Goto(cont_label))]
                basic_blocks[test_label] = explicate_stmts(condition_stmts, test_stmts)
                return [cfun.Goto(test_label)]
            case If(condition, then_stmts, else_stmts):
                cont_label = create_block(cont)
                e2_label = create_block(explicate_stmts(then_stmts, [cfun.Goto(cont_label)]))
                e3_label = create_block(explicate_stmts(else_stmts, [cfun.Goto(cont_label)]))
                return [cfun.If(explicate_exp(condition),
                                cfun.Goto(e2_label),
                                cfun.Goto(e3_label))]
            case _:
                raise RuntimeError(stmt)

    def explicate_stmts(stmts: List[Stmt], cont: List[cfun.Stmt]) -> List[cfun.Stmt]:
        for s in reversed(stmts):
            cont = explicate_stmt(s, cont)
        return cont

    new_body = [cfun.Return(cfun.Constant(0))]
    new_body = explicate_stmts(prog.stmts, new_body)


    basic_blocks['mainstart'] = new_body
    functions.append(cfun.CFunctionDef('main', [], basic_blocks))
    # Now return a list of function defs
    return cfun.CProgram(functions)



##################################################
# select-instructions
##################################################
# op           ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#                | "subscript" | "allocate" | "collect" | "tuple_set"
# Atm          ::= Var(x) | Constant(n)
# Expr         ::= Atm | Prim(op, List[Expr])
# Stmt         ::= Assign(x, Expr) | Print(Expr)
#                | If(Expr, Goto(label), Goto(label)) | Goto(label) | Return(Expr)
# Stmts        ::= List[Stmt]
# CFunctionDef ::= CFunctionDef(name, List[str], Dict[label, Stmts])
# Cfun         ::= CProgram(List[CFunctionDef])

@dataclass(frozen=True, eq=True)
class X86FunctionDef(AST):
    label: str
    blocks: Dict[str, List[x86.Instr]]
    stack_space: Tuple[int, int]

@dataclass(frozen=True, eq=True)
class X86ProgramDefs(AST):
    defs: List[X86FunctionDef]

def select_instructions(prog: cfun.CProgram) -> X86ProgramDefs:
    """
    Transforms a Ltup program into a pseudo-x86 assembly program.
    :param prog: a Ltup program
    :return: a pseudo-x86 program
    """
    current_function = 'main'  # This is going to change regardless so changeable

    #TODO: FROM INSTRUCTOR SOLUTION OF 6:
    def si_atm(a: cfun.Expr) -> x86.Arg:
        match a:
            case cfun.Constant(i):
                return x86.Immediate(int(i))
            case cfun.Var(x):
                if x in global_values:
                    return x86.GlobalVal(x)
                else:
                    return x86.Var(x)
            case _:
                raise Exception('si_atm', a)

    def si_stmts(stmts: List[cfun.Stmt]) -> List[x86.Instr]:
        instrs = []

        for stmt in stmts:
            instrs.extend(si_stmt(stmt))

        return instrs

    op_cc = {'eq': 'e', 'gt': 'g', 'gte': 'ge', 'lt': 'l', 'lte': 'le'}

    binop_instrs = {'add': 'addq', 'sub': 'subq', 'mult': 'imulq', 'and': 'andq', 'or': 'orq'}

    def si_stmt(stmt: cfun.Stmt) -> List[x86.Instr]:
        match stmt:
            #TODO: New cases here
            case cfun.Assign(x, cfun.Var(f)):
                #TODO
                pass
            case cfun.Call(fun, args):
                pass
            case cfun.Assign(x, cfun.Prim('allocate', [cfun.Constant(num_bytes), cfun.Constant(tag)])):
                return [x86.NamedInstr('movq', [x86.GlobalVal('free_ptr'), x86.Var(x)]),
                        x86.NamedInstr('addq', [x86.Immediate(num_bytes), x86.GlobalVal('free_ptr')]),
                        x86.NamedInstr('movq', [x86.Var(x), x86.Reg('r11')]),
                        x86.NamedInstr('movq', [x86.Immediate(tag), x86.Deref('r11', 0)])]
            case cfun.Assign(_, cfun.Prim('tuple_set', [cfun.Var(x), cfun.Constant(offset), atm1])):
                offset_bytes = 8 * (offset + 1)
                return [x86.NamedInstr('movq', [x86.Var(x), x86.Reg('r11')]),
                        x86.NamedInstr('movq', [si_atm(atm1), x86.Deref('r11', offset_bytes)])]
            case cfun.Assign(x, cfun.Prim('subscript', [atm1, cfun.Constant(offset)])):
                offset_bytes = 8 * (offset + 1)
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('r11')]),
                        x86.NamedInstr('movq', [x86.Deref('r11', offset_bytes), x86.Var(x)])]
            case cfun.Assign(_, cfun.Prim('collect', [cfun.Constant(num_bytes)])):
                return [x86.NamedInstr('movq', [x86.Reg('r15'), x86.Reg('rdi')]),
                        x86.NamedInstr('movq', [x86.Immediate(num_bytes), x86.Reg('rsi')]),
                        x86.Callq('collect')]

            case cfun.Assign(x, cfun.Prim(op, [atm1, atm2])):
                if op in binop_instrs:
                    return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('rax')]),
                            x86.NamedInstr(binop_instrs[op], [si_atm(atm2), x86.Reg('rax')]),
                            x86.NamedInstr('movq', [x86.Reg('rax'), x86.Var(x)])]
                elif op in op_cc:
                    return [x86.NamedInstr('cmpq', [si_atm(atm2), si_atm(atm1)]),
                            x86.Set(op_cc[op], x86.ByteReg('al')),
                            x86.NamedInstr('movzbq', [x86.ByteReg('al'), x86.Var(x)])]

                else:
                    raise Exception('si_stmt failed op', op)
            case cfun.Assign(x, cfun.Prim('not', [atm1])):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Var(x)]),
                        x86.NamedInstr('xorq', [x86.Immediate(1), x86.Var(x)])]
            case cfun.Assign(x, atm1):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Var(x)])]
            case cfun.Print(atm1):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('rdi')]),
                        x86.Callq('print_int')]
            case cfun.Return(atm1):
                return [x86.NamedInstr('movq', [si_atm(atm1), x86.Reg('rax')]),
                        x86.Jmp('conclusion')]
            case cfun.Goto(label):
                return [x86.Jmp(label)]
            case cfun.If(a, cfun.Goto(then_label), cfun.Goto(else_label)):
                return [x86.NamedInstr('cmpq', [si_atm(a), x86.Immediate(1)]),
                        x86.JmpIf('e', then_label),
                        x86.Jmp(else_label)]
            case _:
                raise Exception('si_stmt', stmt)

    def si_def(d: cfun.CFunctionDef) -> X86FunctionDef:
        # TODO: Fill in using exercise function 2
        nonlocal current_function
        current_function = d.name
        for label in d.blocks:
            si_stmts(d.blocks[label])
            if label == d.name + 'start':

            si_stmts(d.blocks[label])
        return X86FunctionDef(d.name, blocks, (None, None))

    # basic_blocks = {label: si_stmts(block) for (label, block) in prog.blocks.items()}
    functions = []
    for d in prog.defs:
        functions.append(si_def(d))
    return X86ProgramDefs(functions)


##################################################
# allocate-registers
##################################################
# Arg            ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op             ::= 'addq' | 'subq' | 'imulq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
#                  | 'leaq'
# cc             ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr          ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#                  | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#                  | IndirectCallq(Arg)
# Blocks         ::= Dict[label, List[Instr]]
# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

Color = x86.Arg
Coloring = Dict[x86.Var, x86.Arg]
Saturation = Set[x86.Arg]

def allocate_registers(program: X86ProgramDefs) -> X86ProgramDefs:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    pass    


def _allocate_registers(name: str, program: x86.X86Program) -> x86.X86Program:
    pass


##################################################
# patch-instructions
##################################################
# Arg            ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op             ::= 'addq' | 'subq' | 'imulq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
#                  | 'leaq'
# cc             ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr          ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#                  | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#                  | IndirectCallq(Arg)
# Blocks         ::= Dict[label, List[Instr]]
# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

def patch_instructions(program: X86ProgramDefs) -> X86ProgramDefs:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    pass


def _patch_instructions(program: x86.X86Program) -> x86.X86Program:
    pass


##################################################
# prelude-and-conclusion
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Deref(r, offset) | GlobalVal(x)
# op     ::= 'addq' | 'subq' | 'imulq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq'
#          | 'leaq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= NamedInstr(op, List[Arg]) | Callq(label) | Retq()
#          | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#          | IndirectCallq(Arg)
# Blocks ::= Dict[label, List[Instr]]
# X86    ::= X86Program(Blocks)

def prelude_and_conclusion(program: X86ProgramDefs) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    pass


def _prelude_and_conclusion(name: str, program: x86.X86Program) -> x86.X86Program:
    pass


##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'typecheck2': typecheck,
    'expose allocation': expose_alloc,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86
}


def run_compiler(s, logging=False):
    global global_logging

    old_logging = global_logging
    global_logging = logging

    def print_prog(current_program):
        print('Concrete syntax:')
        if isinstance(current_program, x86.X86Program):
            print(x86.print_x86(current_program))
        elif isinstance(current_program, X86ProgramDefs):
            print(print_x86defs.print_x86_defs(current_program))
        elif isinstance(current_program, Program):
            print(print_program(current_program))
        elif isinstance(current_program, cfun.CProgram):
            print(cfun.print_program(current_program))

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

    global_logging = old_logging
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

