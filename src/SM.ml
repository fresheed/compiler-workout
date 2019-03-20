open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
(* let rec eval env conf prog = failwith "Not yet implemented" *)
let rec eval env config2 program =
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
     | config2, cmd::rest -> eval env (eval_cmd config2 cmd) rest(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2)  -> compile s1 @ compile s2
  | Stmt.Read x        -> [READ; ST x]
  | Stmt.Write e       -> expr e @ [WRITE]
  | Stmt.Assign (x, e) -> expr e @ [ST x]
