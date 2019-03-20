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
let rec eval env (stack, (state, inp, out as subconf) as config2) program =
  let eval_expr expr = Language.Expr.eval state expr in
  let eval_cmd config command = match config, command with
    | (y::x::rest, _), BINOP (str_op)
      -> let result=Language.Expr.eval state (Language.Expr.Binop (str_op, Language.Expr.Const (x), Language.Expr.Const (y)))
         in (result::rest, subconf)
              
    | (_, _), CONST (value) -> (value::stack, subconf)
    | (_, (_, value::rest, _)), READ -> (value::stack, (state, rest, out))
    | (value::rest, (_, _, _)), WRITE -> (rest, (state, inp, out@[value]))
    | (_, _), LD (var) -> ((state var)::stack, subconf)
    | (value::rest, _), ST (var) -> (rest, (Language.Expr.update var value state, inp, out))
    | _, LABEL _ -> config

  in match program with
     | [] -> config2
     | (JMP label)::_ -> eval env config2 (env#labeled label)
     | (CJMP (mode, label))::next ->
        let top::rest = stack in
        let goto = (env#labeled label) in
        let target = if ((mode=="z") == (top == 0)) then goto else next in
        eval env (rest, subconf) target
     (* other *)
     | cmd::rest -> eval env (eval_cmd config2 cmd) rest

(* Top-level evaluation

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
class compiler =
  object (self)
    val label_count = 0

    method next_label = {< label_count = label_count+1 >}
    method get_if_labels =
      let suffix = string_of_int label_count
      in "else_" ^ suffix, "fi_" ^ suffix, self#next_label
    method get_while_labels =
      let suffix = string_of_int label_count
      in "loop_" ^ suffix, "od_" ^ suffix, self#next_label
  end

let rec compile =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec compile_impl compiler = function
    | Stmt.Seq (s1, s2)  -> compile_impl compiler s1 @ compile_impl compiler s2
    | Stmt.Read x        -> [READ; ST x]
    | Stmt.Write e       -> expr e @ [WRITE]
    | Stmt.Assign (x, e) -> expr e @ [ST x]
    | Stmt.Skip -> []
    | Stmt.If (cond, positive, negative) ->
       let else_label, fi_label, compiler' = compiler#get_if_labels in
       expr cond @ [CJMP ("z", else_label)] @ compile_impl compiler' positive
       @ [JMP fi_label; LABEL else_label] @ compile_impl compiler' negative
       @ [LABEL fi_label]
    | Stmt.While (cond, body) -> 
       let loop_label, od_label, compiler' = compiler#get_while_labels in
       [LABEL loop_label] @ expr cond @ [CJMP ("z", od_label)]
       @ compile_impl compiler' body @ [JMP loop_label; LABEL od_label]
  in compile_impl (new compiler)

         
