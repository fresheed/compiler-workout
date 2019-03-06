open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config2 program =
  let eval_cmd config command = match config, command with
    | (y::x::stack, ((state, inp, out) as subconf)), BINOP (str_op)
      -> let result=Language.Expr.eval state (Language.Expr.Binop (str_op, Language.Expr.Const (x), Language.Expr.Const (y)))
         in (result::stack, subconf)
    | (stack, subconf), CONST (value) -> (value::stack, subconf)
    | (stack, (state, value::inp, out)), READ -> (value::stack, (state, inp, out))
    | (value::stack, (state, inp, out)), WRITE -> (stack, (state, inp, out@[value]))
    | (stack, ((state, _, _) as subconf)), LD (var) -> ((state var)::stack, subconf)
    | (value::stack, (state, inp, out)), ST (var) -> (stack, (Language.Expr.update var value state, inp, out))
  in match config2, program with
     | config2, [] -> config2
     | config2, cmd::rest -> eval (eval_cmd config2 cmd) rest
(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile program =
  let rec compile_expr expr = match expr with
    | Language.Expr.Const n -> [CONST n]
    | Language.Expr.Var x -> [LD x]
    | Language.Expr.Binop (op_str, e1, e2) -> compile_expr e1 @ compile_expr e2 @ [BINOP op_str]
  in match program with
     | Language.Stmt.Read (var) -> [READ; ST var]
     | Language.Stmt.Write (expr) -> compile_expr expr @ [WRITE]
     | Language.Stmt.Assign (var, expr) -> compile_expr expr @ [ST var]
     | Language.Stmt.Seq (p1, p2) -> compile p1 @ compile p2
