(* Simple expressions: syntax and semantics *)

(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
             
(* The type for the expression. Note, in regular OCaml there is no "@type..." 
   notation, it came from GT. 
*)
@type expr =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * expr * expr with show

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

(* An example of a non-trivial state: *)                                                   
let s = update "x" 1 @@ update "y" 2 @@ update "z" 3 @@ update "t" 4 empty

(* Some testing; comment this definition out when submitting the solution. *)
(* let _ =
 *   List.iter
 *     (fun x ->
 *        try  Printf.printf "%s=%d\n" x @@ s x
 *        with Failure s -> Printf.printf "%s\n" s
 *     ) ["x"; "a"; "y"; "z"; "t"; "b"] *)

(* Expression evaluator

     val eval : state -> expr -> int
 
   Takes a state and an expression, and returns the value of the expression in 
   the given state.
 *)

let rec eval st ex  = match ex with
  | Const (value) -> value
  | Var (name) -> st name
  | Binop (op_str, arg1, arg2) ->
     let conv = fun op a1 a2 -> if (op a1 a2) then 1 else 0 in
     let op_mapping = [
         ("!!", conv (fun x y -> (x != 0 || y !=0)));
         ("&&", conv (fun x y -> (x != 0 && y !=0)));
         ("==", conv (==));
         ("!=", conv (!=));
         ("<=", conv (<=));
         ("<", conv (<));
         (">=", conv (>=));
         (">", conv (>));
         ("+", (+));
         ("-", (-));
         ("*", ( * ));
         ("/", (/));
         ("%", (mod));
       ]
     in (List.assoc op_str op_mapping) (eval st arg1) (eval st arg2)
;;
                    
