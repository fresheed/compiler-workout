(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
open Combinators


(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    (* let update_array  a i x = List.init (List.length a) (fun j -> if j = i then x else List.nth a j) *)
    let update_array a i x = List.mapi (fun j v -> if j = i then x else v) a;

  end
       
let to_list = function
  | None -> []
  | Some results -> results

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  ->
       (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
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

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, (r : Value.t option)) as conf) expr =
      let set_result res = (st, i, o, Some res) in
      match expr with
      | Const n -> set_result (Value.of_int n)
      | Var   x -> set_result (State.eval st x)
      | Binop (op, x, y) ->
         let (st', i', o', Some (Value.Int a1) as after_first) = eval env conf x in
         let (st'', i'', o'', Some (Value.Int a2)) = eval env after_first y in
         let result = to_func op (a1) (a2) in
         (st'', i'', o'', Some (Value.of_int result))
      | Call (func, args_exprs) ->
         let eval_arg (conf, results) expr =
           let (_, _, _, Some (Value.Int res) as conf') = eval env conf expr
           in (conf', results@[Value.of_int res]) in
         let (config', args_values) =
           List.fold_left eval_arg (conf, []) args_exprs in
         env#definition env func args_values config'
      (* | Array values -> set_result (Value.of_array values) *)
      | String str -> set_result (Value.of_string str)
      | Array exprs ->
         let (st', i', o', values) = eval_list env conf exprs in
         env#definition env "$array" values (st', i', o', None)
      | Elem (seq_expr, index_expr) -> 
         let (st', i', o', args) = eval_list env conf [seq_expr; index_expr]
         in env#definition env "$elem" args (st', i', o', None)
      | Length expr ->
         let (st', i', o', Some value) = eval env conf expr
         in env#definition env "$length" [value] (st', i', o', None)
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
     *)

    let e2s = GT.transform(t) (new @t[show]) ()
    let el2sl exprs = String.concat "," (List.map e2s exprs)

    let rec build_index_sequence expr indices = match indices with
      | [] -> expr
      | index::rest -> build_index_sequence (Elem (expr, index)) rest

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
      
      (* args_list: arg:parse "," rest:args_list {arg::rest} | arg:parse {[arg]}; *)
      args_list: -"(" !(Util.list0)[parse] -")";
      funcall: fnc:IDENT args:args_list {Call (fnc, args)};

      main: (* no left recursion *)
        -"(" parse -")"
        | funcall
        | n:DECIMAL {Const n}
        | x:IDENT   {Var x}
        | "[" elements:!(Util.list0)[parse] "]" {Array elements}
        | s:STRING {String (String.sub s 1 ((String.length s)-2))}
        | c:CHAR {Const (Char.code c)};

      index: -"[" ix:parse -"]" {ix};
      indices_seq: inds:(index*) {inds};
      indexed: arr:main inds:indices_seq {build_index_sequence arr inds};
      primary:
        arr:indexed ".length" {Length arr}
        | indexed
    )    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
          
    let rec eval env (state, input, output, (res : Value.t option) as config) kontinue program =
      let eval_expr_now expr = Expr.eval env config expr in
      let set_var var value = State.update var value state in
      let prepend_kontinue stmt kont = match kont with
        | Skip -> stmt
        | _ -> Seq (stmt, kont) in
      match program with
      | Skip -> (match kontinue with
                | Skip -> config
                | _ -> eval env config Skip kontinue)
      (* | Read (var) ->
       *    let value::inp_rest = input in
       *    eval env (set_var var value, inp_rest, output, None) Skip kontinue
       * | Write (expr) ->
       *    let (state', inp', out', Some res) = eval_expr_now expr in
       *    eval env (state', inp', out'@[to_int res], None) Skip kontinue *)
      | Assign (var, indices, expr) ->
      (* eval env (State.update var res state', inp', out', None) Skip kontinue *)
         let (st', i', o', args_values) = Expr.eval_list env config indices in
         let (st'', i'', o'', Some value) = Expr.eval env (st', i', o', None) expr in
         let st''' = update st'' var value args_values in
         eval env (st''', i'', o'', None) Skip kontinue
      | Seq (prog1, prog2) ->         
         (* eval env (eval env config kontinue prog1) kontinue prog2 *)
         eval env config (prepend_kontinue prog2 kontinue) prog1
      | If (cond, positive, negative) ->
         let (_, _, _, Some (Value.Int res) as after_cond_eval) = eval_expr_now cond in
         if (res !=0)
         then eval env after_cond_eval kontinue positive
         else eval env after_cond_eval kontinue negative
      | (While (cond, body) as loop) ->
         let (_, _, _, Some (Value.Int res) as after_cond_eval) = eval_expr_now cond in
         if (res!=0)
         then eval env after_cond_eval (prepend_kontinue loop kontinue) body
         else eval env after_cond_eval Skip kontinue
      | (Repeat (body, cond) as loop) ->
         let config' = eval env config Skip body in
         let (_, _, _, Some (Value.Int res) as after_cond_eval) = Expr.eval env config' cond in
         if res == 0
         then (* then eval env after_cond_eval kontinue loop *)
           eval env after_cond_eval (prepend_kontinue loop kontinue) Skip (* right? *)
         else eval env after_cond_eval Skip kontinue
      | Call (name, args_exprs) ->
         (* let eval_arg (conf, results) expr =
          *   let (_, _, _, Some (Value.Int res) as conf') = Expr.eval env conf expr
          *   in (conf', results@[Value.of_int res]) in
          * let (config', args_values) =
          *   List.fold_left eval_arg (config, []) args_exprs in *)
         let (st', i', o', args_values) = Expr.eval_list env config args_exprs in
         let after_call = env#definition env name args_values (st', i', o', None) in
         eval env after_call Skip kontinue
      | Return opt -> match opt with
                      | Some expr -> eval_expr_now expr
                      | None -> config
                       
    (* Statement parser *)
    let rec build_ite_tree (cond, positive as if_branch) elif_branches else_branch_opt =
      match elif_branches, else_branch_opt with
      | elif::rest, _ ->
         let subtree = build_ite_tree elif rest else_branch_opt in
         If (cond, positive, subtree)
      | [], None -> If (cond, positive, Skip)
      | [], Some else_cmd -> If (cond, positive, else_cmd)

    let e2s = GT.transform(Expr.t) (new @Expr.t[show]) ()
    let el2sl exprs = String.concat "," (List.map e2s exprs)
                               
    ostap (	  
      base: !(Expr.parse);

      assign: v:IDENT inds:(!(Expr.indices_seq)) ":=" e:base {Assign (v, inds, e)};
      (* read: "read" "(" v:IDENT ")" {Read v};
       * write: "write" "(" e:base ")" {Write e}; *)
      skip: "skip" {Skip};
      args_list: arg:base "," rest:args_list {arg::rest} | arg:base {[arg]};
      call: name:IDENT "(" args:(args_list?) ")" {Call (name, to_list args)};
      return: "return" opt_expr:(base?) {Return opt_expr};
      (* single: assign | read | write | skip | call | return; *)
      single: assign | skip | call | return;

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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
(* =======
 *     ostap (                                      
 *       args_list: arg:IDENT "," rest:args_list {arg::rest} | arg:IDENT {[arg]};
 *       def: "fun" name:IDENT "(" args:args_list? ")" locals:(-"local" lst:args_list)? "{" body:!(Stmt.parse) "}" {name, (to_list args, to_list locals, body)};
 *       parse: def
 * >>>>>>> theirs *)
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
