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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool 
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (cs, ds, (state, inp, out, foo as subconf) as config2) program =
  let eval_cmd config command = match config, command with
    | (_, y::x::rest, _), BINOP (str_op)
      -> let result=Language.Expr.to_func str_op x y
         in (cs, result::rest, subconf)

    | _, CONST (value) -> (cs, value::ds, subconf)
    | (_, _, (_, value::rest, _, _)), READ -> (cs, value::ds, (state, rest, out, foo))
    | (_, value::rest, (_, _, _, _)), WRITE -> (cs, rest, (state, inp, out@[value], foo))
    | _, LD (var) -> (cs, (Language.State.eval state var)::ds, subconf)
    | (_, value::rest, _), ST (var) -> (cs, rest, (Language.State.update var value state, inp, out, foo))
    | _, LABEL _ -> config

  in match program with
     | [] -> config2
     | (JMP label)::_ -> eval env config2 (env#labeled label)
     | (CJMP (mode, label))::next ->
        let top::rest = ds in
        let goto = (env#labeled label) in
        let target = if ((mode="z") == (top == 0)) then goto else next in
        eval env (cs, rest, subconf) target
     | (CALL (name, _, _))::next -> eval env ((next, state)::cs, ds, subconf) (env#labeled name)
     | (BEGIN (_, args, locals))::next ->
        let state_pre = State.enter state (args @ locals) in
        (* args values are on stack *)
        let restore_seq = List.map (fun arg -> ST arg) args in
        let config_before = eval env (cs, ds, (state_pre, inp, out, foo)) restore_seq in
        eval env config_before next
     | RET _::_
     | END::_ -> (match cs with
                 | (prev_prog, prev_state)::rest_cs ->
                    let state_after = State.leave state prev_state in
                    eval env (rest_cs, ds, (state_after, inp, out, foo)) prev_prog
                 | [] -> config2)
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
  let (_, _, (_, _, o, _)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], None)) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

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
    method get_opt_while_labels =
      let suffix = string_of_int label_count
      in "loop_" ^ suffix, "checkwhile_" ^ suffix, self#next_label
    method get_repeatuntil_label =
      let suffix = string_of_int label_count
      in "repeat_" ^ suffix, self#next_label
  end

let rec compile (defs, main_program) =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op] 
  | Expr.Call (name, args_exprs) -> (* has return value *)
     let args_init = List.concat (List.rev (List.map expr args_exprs))
     in args_init @ [CALL (name, List.length args_exprs, true)] in     
  (* it's slow (n^2 for full program) but only at compile time *)
  let rec replace_label old_label new_label program = match program with
    | [] -> []
    | LABEL lbl as orig :: rest -> (if lbl = old_label then [] else [orig]) @ replace_label old_label new_label rest
    | JMP lbl :: rest -> (JMP (if lbl = old_label then new_label else lbl)) :: replace_label old_label new_label rest
    | CJMP (mode, lbl) :: rest -> (CJMP (mode, (if lbl = old_label then new_label else lbl))) :: replace_label old_label new_label rest
    | cmd :: rest -> cmd :: replace_label old_label new_label rest in

  let rec compile_impl compiler = function
    | Stmt.Seq (s1, s2)  -> let prog1, compiler' = compile_impl compiler s1 in
                            let prog2, compiler'' = compile_impl compiler' s2 in
                            prog1 @ prog2, compiler''
    | Stmt.Read x        -> [READ; ST x], compiler
    | Stmt.Write e       -> expr e @ [WRITE], compiler
    | Stmt.Assign (x, e) -> expr e @ [ST x], compiler
    | Stmt.Skip -> [], compiler
    | Stmt.If (cond, positive, negative) ->
       let else_label, fi_label, compiler' = compiler#get_if_labels in
       let prog_pos_raw, compiler'' = compile_impl compiler' positive in
       let prog_pos = match (List.rev prog_pos_raw) with
         | LABEL old_label :: _ -> replace_label old_label fi_label prog_pos_raw
         | [] -> []
         | _ -> prog_pos_raw in
       let prog_neg_raw, compiler''' = compile_impl compiler'' negative in
       let prog_neg = match (List.rev prog_neg_raw) with
         | LABEL old_label :: _ -> replace_label old_label fi_label prog_neg_raw
         | [] -> []
         | _ -> prog_neg_raw in
       expr cond @ [CJMP ("z", else_label)]
       @ prog_pos @ [JMP fi_label; LABEL else_label]
       @ prog_neg @ [LABEL fi_label], compiler'''
    | Stmt.While (cond, body) -> 
       let loop_label, check_label, compiler' = compiler#get_opt_while_labels in
       let prog_body, compiler'' = compile_impl compiler' body in       
       [JMP check_label; LABEL loop_label] @ prog_body @ [LABEL check_label]
       @ expr cond @ [CJMP ("nz", loop_label)], compiler''
    | Stmt.Repeat (body, cond) ->
       let loop_label, compiler' = compiler#get_repeatuntil_label in
       let prog_body, compiler'' = compile_impl compiler' body in
       [LABEL loop_label] @ prog_body @ expr cond @ [CJMP ("z", loop_label)], compiler''
    | Stmt.Call (name, args_exprs) ->
       (let args_init = List.concat (List.rev (List.map expr args_exprs)) (* args values on stack top *)
        in args_init @ [CALL (name, List.length args_exprs, false)]), compiler (* no return value *)
    | Stmt.Return opt_value -> (match opt_value with
                               | Some exp -> expr exp @ [RET true]
                               | None -> [RET false]), compiler
  in
  let compile_program program = fst (compile_impl (new compiler) program) in
  let main_program = compile_program main_program in
  let compile_procedure (name, (args, locals, body)) =
    let body_program  = compile_program body in
    [LABEL name; BEGIN (name, args, locals)] @ body_program @ [END] in
  let procedures = List.concat (List.map compile_procedure defs) in
  main_program @ [END] @ procedures
