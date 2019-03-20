(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap.Util
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let conv = fun op a1 a2 -> if (op a1 a2) then 1 else 0

     let lvl4_ops = [ 		(* LA *)
        ("!!", conv (fun x y -> (x != 0 || y !=0)));	
      ]
    let lvl3_ops = [ 		(* LA *)
        ("&&", conv (fun x y -> (x != 0 && y !=0)));
      ]
    let lvl2_ops = [ 		(* NA *)
        ("==", conv (==));
        ("!=", conv (!=));
        ("<=", conv (<=));
        ("<", conv (<));
        (">=", conv (>=));
        (">", conv (>));	
      ]
    let lvl1_ops = [		(* LA *)
	("+", (+));
        ("-", (-));	
      ]
    let lvl0_ops = [		(* LA *)
        ("*", ( * ));
        ("/", (/));
        ("%", (mod));
      ]
    let op_mapping = lvl4_ops @ lvl3_ops @ lvl2_ops @ lvl1_ops @ lvl0_ops
    let rec eval st ex  = match ex with
      | Const (value) -> value
      | Var (name) -> st name
      | Binop (op_str, arg1, arg2) ->
      	 (List.assoc op_str op_mapping) (eval st arg1) (eval st arg2)
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    let wrap_binop symbol = fun x y -> Binop (symbol, x, y)
    ostap (
      parse:
	!(Ostap.Util.expr 
	    (fun x -> x)
	     [|
	       (* this is obviously redundant, but I haven't succeeded in refactoring it with List.map *)
	       `Lefta, [ostap ("!!"), wrap_binop "!!";];
	       `Lefta, [ostap ("&&"), wrap_binop "&&";];
	       `Nona, [ostap ("=="), wrap_binop "==";
		       ostap ("!="), wrap_binop "!=";
		       ostap ("<="), wrap_binop "<=";
		       ostap ("<"), wrap_binop "<";
		       ostap (">="), wrap_binop ">=";
		       ostap (">"), wrap_binop ">";];
	       `Lefta, [ostap ("+"), wrap_binop "+";
			ostap ("-"), wrap_binop "-";];
	       `Lefta, [ostap ("*"), wrap_binop "*";
			ostap ("/"), wrap_binop "/";
			ostap ("%"), wrap_binop "%";];	       
      	     |]
	    primary
	);
      primary: v:IDENT {Var v} | n:DECIMAL {Const n} | -"(" parse -")"
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
    (* loop with a post-condition       *) (* add yourself *)  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, input, output as config) program =
      let eval_expr expr = Expr.eval state expr in
      let set_var var value = Expr.update var value state in
      match config, program with
      | (_, value::inp_rest, out), Read (var) -> (set_var var value, inp_rest, out)
      | (state, inp, out), Write (expr) -> (state, inp, out@[eval_expr expr])
      | (_, inp, out), Assign (var, expr) -> (set_var var (eval_expr expr), inp, out)
      | _, Seq (prog1, prog2) -> eval (eval config prog1) prog2
      | _, Skip -> config
      | _, If (cond, positive, negative) -> if (eval_expr cond) != 0
                                            then eval config positive
                                            else eval config negative
      | _, (While (cond, body) as loop) -> if (eval_expr cond) != 0
                                           then eval config (Seq (body, loop))
                                           else config (* don't use skip *)
                                   
    (* Statement parser *)
    ostap (	  
      base: !(Expr.parse);

      assign: v:IDENT ":=" e:base {Assign (v, e)};
      read: "read" "(" v:IDENT ")" {Read v};
      write: "write" "(" e:base ")" {Write e};
      skip: "skip" {Skip};
      single: assign | read | write | skip;
                                      
      ite: "if" cond:base "then" positive:parse "else" negative:parse "fi" {If (cond, positive, negative)};
      while_loop: "while" cond:base "do" body:parse "od" {While (cond, body)};
      grouped: ite | while_loop;
      seq: cmd1:(single | grouped)  ";" cmd2:parse {Seq (cmd1, cmd2)};

      parse: seq | grouped | single
    )      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
