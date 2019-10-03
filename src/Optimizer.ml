open GT
open Language

module ExtStmt =
  struct

    @type t =
      (* read into the variable           *) | ExtRead   of int * string
      (* write the value of an expression *) | ExtWrite  of int * Expr.t
      (* assignment                       *) | ExtAssign of int * string * Expr.t
      (* composition                      *) | ExtSeq    of int * t * t
      (* empty statement                  *) | ExtSkip of int
      (* conditional                      *) | ExtIf     of int * Expr.t * t * t
      (* loop with a pre-condition        *) | ExtWhile  of int * Expr.t * t
      (* loop with a post-condition       *) | ExtRepeatUntil of int * Expr.t * t with show

    let get_label estmt = match estmt with
      | ExtRead (i, _) | ExtWrite (i, _) | ExtAssign (i, _, _) | ExtSeq (i, _, _)
      | ExtSkip (i) | ExtIf (i, _, _, _) | ExtWhile (i, _, _) | ExtRepeatUntil (i, _, _) -> i

    let enhance prog =
      let rec enhance_ stmt num = match stmt with
        | Stmt.Seq (s1, s2)  -> let es1 = enhance_ s1 (num) in
                                let es2 = enhance_ s2 (get_label es1 + 1) in
                                ExtSeq (get_label es2 + 1, es1, es2)
        | Stmt.If (cond, s1, s2) -> let es1 = enhance_ s1 (num) in
                                    let es2 = enhance_ s2 (get_label es1 + 1) in
                                    ExtIf (get_label es2 + 1, cond, es1, es2)
        | Stmt.While (cond, s) -> let es = enhance_ s (num) in ExtWhile (get_label es + 1, cond, es)
        | Stmt.RepeatUntil (cond, s) -> let es = enhance_ s (num) in ExtRepeatUntil (get_label es + 1, cond, es)
        | Stmt.Read (s) -> ExtRead (num, s)
        | Stmt.Write (e) -> ExtWrite (num, e)
        | Stmt.Assign (x, e) -> ExtAssign (num, x, e)
        | Stmt.Skip -> ExtSkip (num)
      in enhance_ prog 0

    let tostring eprog lbl_proc =
      let rec show_ stmt shift =
        let next = String.concat "" [" "; shift] in
        let show_expr = show(Language.Expr.t) in
        let describe stmt = (match stmt with
        | ExtSeq (i, s1, s2)  -> Printf.sprintf "%s%s;\n%s%s\n" shift (show_ s1 shift) shift (show_ s2 shift)
        | ExtIf (i, cond, s1, s2) -> Printf.sprintf "%sif (%s)\n%sthen\n%s\n%selse\n%s\n%sfi"
                                     shift (show_expr cond) shift (show_ s1 next) shift (show_ s2 next) shift
        | ExtWhile (i, cond, s) -> Printf.sprintf "%swhile (%s)\n%s\n" shift (show_expr cond) (show_ s next)
        | ExtRepeatUntil (i, cond, s) -> Printf.sprintf "%srepeat\n%s\n%suntil (%s)" shift (show_ s next) shift (show_expr cond)
        | s -> Printf.sprintf "%s%s" shift (show(t) s)) in
(*        | ExtRead (i, s) -> ExtRead (num, s)*)
(*        | ExtWrite (i, e) -> ExtWrite (num, e)*)
(*        | ExtAssign (i, x, e) -> ExtAssign (num, x, e)*)
(*        | ExtSkip (i) -> ExtSkip (num)*)
        let print_ext stmt  = (match stmt with
          | ExtSeq _ as es -> describe es
          | other -> Printf.sprintf "%d: %s #%s" (get_label stmt) (describe stmt) (lbl_proc (get_label stmt))) in
        print_ext stmt
      in show_ eprog ""

end


let optimize orig_prog =
  let prog = ExtStmt.enhance orig_prog in
  Printf.eprintf "program: \n%s\n" (ExtStmt.tostring prog  (fun lbl -> "()"));
  (*List.iter (fun i -> Printf.printf "%s\n\!" (show(insn) i))*)
  orig_prog

