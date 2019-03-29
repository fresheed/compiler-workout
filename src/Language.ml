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
    let push_scope st xs = {empty with g = st.g; scope = xs} (* enter *)

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g} (* leave *)

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
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
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (state, input, output as config) program =
      let eval_expr expr = Expr.eval state expr in
      let set_var var value = State.update var value state in
      match program with
      | Read (var) ->
         (match input with
          | value::inp_rest -> (set_var var value, inp_rest, output)
          | _ -> failwith "Input stream is empty")
      | Write (expr) -> (state, input, output@[eval_expr expr])
      | Assign (var, expr) -> (set_var var (eval_expr expr), input, output)
      | Seq (prog1, prog2) -> eval env (eval env config prog1) prog2
      | Skip -> config
      | If (cond, positive, negative) -> if (eval_expr cond) != 0
                                         then eval env config positive
                                         else eval env config negative
      | (While (cond, body) as loop) -> if (eval_expr cond) != 0
                                        then eval env config (Seq (body, loop))
                                        else config
      | (Repeat (body, cond) as loop) ->
         let (state', input', output' as config') = eval env config body in
         if (Expr.eval state' cond) == 0
         then eval env config' loop
         else config'
      | Call (name, args_exprs) ->
         let args_values = List.map eval_expr args_exprs in
         let (args, locals, body) = env#definition name in
         let state_pre = State.push_scope state (args @ locals) in
         let set_var st var value = State.update var value st in
         let state_before = List.fold_left2 set_var state_pre args args_values in
         let (state', input', output') = eval env (state_before, input, output) body in
         let state_after = State.drop_scope state' state in
         (state_after, input', output')
                       
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
