(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

let to_list = function
  | None -> []
  | Some results -> results

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) expr =
      let set_result res = (st, i, o, Some res) in
      match expr with
      | Const n -> set_result n
      | Var   x -> set_result (State.eval st x)
      | Binop (op, x, y) ->
         let (st', i', o', Some a1 as after_first) = eval env conf x in
         let (st'', i'', o'', Some a2) = eval env after_first y in
         let result = to_func op a1 a2 in
         (st'', i'', o'', Some result)
             
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    (* let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemnted" *)         
    let rec eval env (state, input, output, res as config) kontinue program =
      let eval_expr_now expr = Expr.eval env config expr in
      let set_var var value = State.update var value state in
      match program with
      | Read (var) ->
         (match input with
          | value::inp_rest -> (set_var var value, inp_rest, output, None)
          | _ -> failwith "Input stream is empty")
      | Write (expr) ->
         let (state', inp', out', Some res) = eval_expr_now expr in
         (state', inp', out'@[res], None)
      | Assign (var, expr) -> 
         let (state', inp', out', Some res) = eval_expr_now expr in
         (State.update var res state', inp', out', None)
      | Seq (prog1, prog2) ->         
         eval env (eval env config kontinue prog1) kontinue prog2
      | Skip -> config
      | If (cond, positive, negative) ->
         let (_, _, _, Some res as after_cond_eval) = eval_expr_now cond in
         if (res!=0)
         then eval env after_cond_eval kontinue positive
         else eval env after_cond_eval kontinue negative
      | (While (cond, body) as loop) ->
         let (_, _, _, Some res as after_cond_eval) = eval_expr_now cond in
         if (res!=0)
         then eval env after_cond_eval kontinue (Seq (body, loop))
         else after_cond_eval
      | (Repeat (body, cond) as loop) ->
         let config' = eval env config kontinue body in
         let (_, _, _, Some res as after_cond_eval) = Expr.eval env config' cond in
         if res == 0
         then eval env after_cond_eval kontinue loop
         else after_cond_eval
      | Call (name, args_exprs) ->
         let eval_arg (conf, results) expr =
           let (_, _, _, Some res as conf') = Expr.eval env conf expr
           in (conf', results@[res]) in
         let (config', args_values) =
           List.fold_left eval_arg (config, []) args_exprs in
         env#definition env name args_values config'
                       
    (* Statement parser *)
    let rec build_ite_tree (cond, positive as if_branch) elif_branches else_branch_opt =
      match elif_branches, else_branch_opt with
      | elif::rest, _ ->
         let subtree = build_ite_tree elif rest else_branch_opt in
         If (cond, positive, subtree)
      | [], None -> If (cond, positive, Skip)
      | [], Some else_cmd -> If (cond, positive, else_cmd)

    ostap (	  
      base: !(Expr.parse);

      assign: v:IDENT ":=" e:base {Assign (v, e)};
      read: "read" "(" v:IDENT ")" {Read v};
      write: "write" "(" e:base ")" {Write e};
      skip: "skip" {Skip};
      args_list: arg:base "," rest:args_list {arg::rest} | arg:base {[arg]};
      call: name:IDENT "(" args:(args_list?) ")" {Call (name, to_list args)};
      single: assign | read | write | skip | call;

      if_then_branch: "if" cond:base "then" positive:parse {(cond, positive)};
      elif_branch: "elif" cond:base "then" positive:parse {(cond, positive)};
      else_branch: "else" negative:parse {negative};
      ite: itb:if_then_branch elifbs:(elif_branch*) ebopt:(else_branch?) "fi" {build_ite_tree itb elifbs ebopt};
      while_loop: "while" cond:base "do" body:parse "od" {While (cond, body)};
      repeat_loop: "repeat" body:parse "until" cond:base {Repeat (body, cond)};
      for_loop: "for" init:parse "," cond:base "," update:parse "do" body:parse "od" {Seq (init, While (cond, Seq (body, update)))};
      grouped: ite | while_loop | repeat_loop | for_loop;
      seq: cmd1:(single | grouped)  ";" cmd2:parse {Seq (cmd1, cmd2)};

      parse: seq | grouped | single
                                     (* todo new stmts *)
    )      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      args_list: arg:IDENT "," rest:args_list {arg::rest} | arg:IDENT {[arg]};
      def: "fun" name:IDENT "(" args:args_list? ")" locals:(-"local" lst:args_list)? "{" body:!(Stmt.parse) "}" {name, (to_list args, to_list locals, body)};
      parse: def
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
