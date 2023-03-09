# Compiler Passes

For each of the following passes, what is its purpose? What property is true of its output?

 - remove-complex-operations
   - Assembly language doesn't take in nested instructions. Arguments need to be atomic.
     - Atomic:
       - Register
       - Memory location
       - Constant
     - Example of non-atomic:<pre><code>Python:
     x = 1 + 2 + 3
     </code></pre>
       <pre><code>
       bad Assembly
       movq $2, %rax
       addq $1, ($addq $3, %rax)
       </code></pre>
     </code></pre>
       <pre><code>
       good Assembly
       movq $2, %rax
       addq $3, %rax
       addq $1, %rax
       </code></pre>
     - Code Example of how we built the pass:
       </code></pre>
            
            def rco(prog: Program) -> Program:
            
                 def rco_exp(e: Expr, bindings: Dict[str, Expr]) -> Expr:
                     match e:
                         case Constant(n):
                         case Var(x):
                         case Prim(op, args):
            
                 def rco_stmt(s: Stmt, bindings: Dict[str, Expr]) -> Stmt:
                     match s:
                         case Assign(x, e): return Assign(x, rco_exp(e, bindings))
                         case Print(e):
                         case _:
            
                 def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
                     new_stmts = []
                     for stmt in stmts: 
                        rco_stmts(stmt)
                     return new_stmts
            
                 return Program(rco_stmts(prog.stmts))
</code></pre>

 - select-instructions
   - It breaks down the abstract syntax of the input program making it into pseudo-x86
- Code: Takes a language and returns a pseudo x86 Program
   <pre><code>
   def si_atm(atm: Expr) -> x86.Arg:
       match atm:
          case Var(x):
              return x86.Var(x)
          case Constant(n):
              return x86.Immediate(n)
          case _:
              raise Exception('si_atm', atm)
        
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
           case _:
              raise Exception('si_stmt', stmt)
        
   def si_stmts(stmts: List[Stmt]) -> List[x86.Instr]:   
</code></pre>
   
 - assign-homes (A2)
   - This pass assigns variables from the pseudo language returned by si into memory locations
     - keep a dict called homes and either assign variables to it or use the location stored for a variable in there
   - %rdp is the register typically used as a reference to offset from for memory locations
     - Ex: movq $1 -8(5rbp)
     - Stack space needs to be allocated (preludes and conclusions)
     - multiple of 16 needed for total space
 - allocate-registers (A3)
   - close as possible to an optimal assignment of variables to registers
   - Steps
     - Build live-after sets (liveness analysis)
     - Build Interference Graph from the live-after sets
     - Color the graph using a graph coloring algorithm
     - For each color assign a register and then use memory addresses after those run out
 - typecheck (A4)
   - look through program and throw an error if there is a type error
   - essentially making design decisions for what should be allowed
     - should a boolean and integer be allowed to be added?
 - explicate-control (A4)
   - how do you handle if statements?
   - turns structured control flow (if) -> program that uses jmp statements
   - intermediately uses Cif
 - patch-instructions
   - looks for instructions that uses two memory storage locations
     - in Assembly we can't pass between memory locations we need one argument as a register
   - uses a register 

# Removing Complex Operands

Which of the following are atomic expressions?

 - 1
   - atomic
 - True
   - atomic
 - 5 + 6
   - not atomic

Perform the remove-complex-opera* pass on this program:

`x = 5 + 6`

<pre><code>
tmp_1 = add(5,6)
x = tmp_1
</code></pre>

`y = x + 7 + 8`
<pre><code>
tmp_1 = add(7,8)
tmp_2 = add(x, tmp_1)
y = tmp_2
</code></pre>

`print(x + y)`

<pre><code>
tmp_1 = add(x,y)
print(tmp_1)
</code></pre>

construct temporary variables

 # x86 / compiler passes / stack allocation

Compile the pseudo-x86 program below into x86, placing all variables on the stack.

`movq $1, x          {}`

`movq $4, tmp_1      {}`

`addq $5, tmp_1      {}`

`movq tmp_1, tmp_2   {}`

`addq x, tmp_2       {}`

`movq tmp_2, %rdi    {}`

`callq print_int     {}`

Part (a): for each variable in the program, assign the variable a home on the stack.

 - x: -8%rbp
 - tmp_1: -16%rbp
 - tmp_2: -24%rbp

Part (b): what is the size (in bytes) of the stack frame for this program?
 - 32 bytes

Part (c): write down the complete x86 program
 - output of assign_homes

<pre><code>

</code></pre>

Liveness analysis / interference graph / graph coloring

Consider this pseudo-x86 program (same as above). Annotate each instruction with its live-after set.

`movq $1, x          {x}`

`movq $4, tmp_1      {x}`

`addq $5, tmp_1      {x, tmp_1}`

`movq tmp_1, tmp_2   {x}`

`addq x, tmp_2       {tmp_2}`

`movq tmp_2, %rdi    {}`

`callq print_int     {}`

Draw the interference graph for this program.
                     

For the following interference graph, assign a register to each variable using saturation-based graph coloring. You may use only the registers rbx and rcx.

 - x: %rbx
 - tmp_1: %rcx
 - tmp_2: %rbx
 - 
### Typechecking
For each of the following programs, determine whether or not the program is well-typed. If it is not well-typed, circle the part of the program containing a type error.

`x = 5`
`print(x)`

well typed

`x = 5`
`x = 6`
`print(x)`

well typed

`x = 5`
`x = True`
`print(x)`

not well typed

`x = 5 + True`
`print(x)`

not well typed

`if 5 == 6:`
    `x = 5`
`else:`
    `x = True`

not well typed

### Control Flow and Control Flow Graphs
For the following program, draw the control flow graph in Cif output by the explicate-control pass.
<pre><code>
if 3 > 4:
    if 4 < 5:
        x = 1
    else:
        x = 2
else:
    x = 3
if 5 == 6:
    x = 5
else:
    x = True
</code>></pre>