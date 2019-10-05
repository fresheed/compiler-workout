open GT
open Language
open Set

module Int' = struct
  type t = int
  let compare x y = Pervasives.compare x y
end
module SetInt = Set.Make(Int')
module Int2' = struct
  type t = int * int
  let compare (x,a) (y, b) = let one = Pervasives.compare x y in if (one != 0) then one else Pervasives.compare a b
end
module SetInt2 = Set.Make(Int2')
module Expr' = struct
  type t = Expr.t
  let compare x y = Pervasives.compare x y
end
module SetExpr = Set.Make(Expr')

let rec show_expr expr = match expr with
| Expr.Const i -> Printf.sprintf "%d" i
| Expr.Var x -> x
| Expr.Binop (op, e1, e2) -> Printf.sprintf "(%s)%s(%s)" (show_expr e1) op (show_expr e2)

let show_list set = (String.concat ", " (List.map show_expr (SetExpr.elements set)))
(*let show_list_labels set = (String.concat ", " (List.map string_of_int (SetInt.elements set)))*)
let show_list_labels lst = (String.concat ", " (List.map string_of_int lst))
let show_flow flow = (String.concat ", " (List.map (fun (x, y) -> Printf.sprintf "%d->%d" x y) flow))


module ExtStmt =  struct
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
        let describe stmt = (match stmt with
        | ExtSeq (i, s1, s2)  -> Printf.sprintf "%s%s;\n%s%s\n" shift (show_ s1 shift) shift (show_ s2 shift)
        | ExtIf (i, cond, s1, s2) -> Printf.sprintf "%sif (%s)\n%sthen\n%s\n%selse\n%s\n%sfi"
                                     shift (show_expr cond) shift (show_ s1 next) shift (show_ s2 next) shift
        | ExtWhile (i, cond, s) -> Printf.sprintf "%swhile (%s)\n%s\n" shift (show_expr cond) (show_ s next)
        | ExtRepeatUntil (i, cond, s) -> Printf.sprintf "%srepeat\n%s\n%suntil (%s)" shift (show_ s next) shift (show_expr cond)
        | ExtRead (_, x) -> Printf.sprintf "%sread (%s)" shift x
        | ExtWrite (_, e) -> Printf.sprintf "%swrite (%s)" shift (show_expr e)
        | ExtAssign (_, x, e) -> Printf.sprintf "%s%s := %s" shift x (show_expr e)
        | ExtSkip _ -> Printf.sprintf "%s// skip" shift) in

        let print_ext stmt  = (match stmt with
          | ExtSeq _ as es -> describe es
          | other -> Printf.sprintf "%d: %s #%s" (get_label stmt) (describe stmt) (lbl_proc (get_label stmt)))
      in  print_ext stmt
    in show_ eprog ""

end

module AnalysisGeneral = struct
    open ExtStmt
    let rec get_init_label estmt = match estmt with
      | ExtSeq (i, s1, s2) -> get_init_label s1
      | ExtIf (i, cond, s1, s2) -> i
      | ExtWhile (i, cond, s) -> i
      | ExtRepeatUntil (i, cond, s) -> get_init_label s
      | es -> get_label es

    let rec get_finish_labels estmt = match estmt with
      | ExtSeq (i, s1, s2) -> get_finish_labels s2
      | ExtIf (i, cond, s1, s2) -> SetInt.union (get_finish_labels s1) (get_finish_labels s2)
      | ExtWhile (i, cond, s) -> SetInt.singleton i
      | ExtRepeatUntil (i, cond, s) -> SetInt.singleton i
      | es -> SetInt.singleton (get_label es)

    let map_to_pairs mapper set_singles = SetInt2.of_list (List.map mapper (SetInt.elements set_singles))

    let rec get_flow stmt =
      let (union, add, empty) = (SetInt2.union, SetInt2.add, SetInt2.empty) in
      match stmt with
      | ExtSeq (i, s1, s2) -> union (union (get_flow s1) (get_flow s2))
                              (let init2 = get_init_label s2 in map_to_pairs (fun x -> (x, init2)) (get_finish_labels s1))
      | ExtIf (i, cond, s1, s2) -> add (i, get_init_label s2)
                                  (add (i, get_init_label s1) (union (get_flow s1) (get_flow s2)))
      | ExtWhile (i, cond, s) -> let init_s = get_init_label s in
                                 add (i, init_s) (union (get_flow s) (map_to_pairs (fun x -> (x, i)) (get_finish_labels s)))
      | ExtRepeatUntil (i, cond, s) -> let init_s = get_init_label s in
                                       add (i, init_s) (union (get_flow s) (map_to_pairs (fun x -> (x, i)) (get_finish_labels s)))
      | es -> empty

    let rec get_dependent_subexprs var expr = match expr with
      | Expr.Const _ -> SetExpr.empty
      | Expr.Var v as cur  -> if (String.equal v var) then SetExpr.singleton cur else SetExpr.empty
      | Expr.Binop (_, e1, e2) as cur -> let subs = SetExpr.union (get_dependent_subexprs var e1) (get_dependent_subexprs var e2)
                                         in if (SetExpr.is_empty subs) then SetExpr.empty else SetExpr.add cur subs

    (* retrieves non-trivial subexpressions *)
    let rec get_all_subexprs expr = match expr with
      | Expr.Binop (_, e1, e2) as cur -> let subs = SetExpr.union (get_all_subexprs e1) (get_all_subexprs e2)
                                         in SetExpr.add cur subs
      | _ -> SetExpr.empty
      

    let prog_exprs prog =
      let rec stmt_exrs stmt = match stmt with
      | ExtSeq (i, s1, s2) -> SetExpr.union (stmt_exrs s1) (stmt_exrs s2)
      | ExtIf (i, cond, s1, s2) -> SetExpr.union (get_all_subexprs cond) (SetExpr.union (stmt_exrs s1) (stmt_exrs s2))
      | ExtWhile (i, cond, s) -> SetExpr.union (get_all_subexprs cond) (stmt_exrs s)
      | ExtRepeatUntil (i, cond, s) -> SetExpr.union (get_all_subexprs cond) (stmt_exrs s)
      | ExtRead (i, x) -> SetExpr.empty
      | ExtWrite (_, e) -> get_all_subexprs e
      | ExtAssign (_, x, e) -> get_all_subexprs e
      | ExtSkip _ -> SetExpr.empty
      in stmt_exrs prog

    let map_build_set emp jn mapper args_list = let results = List.map mapper args_list in
                                    let joined = (match results with
                                    | [] -> emp
                                    | h :: rest -> List.fold_left (fun acc set -> jn acc set) h rest) in
                                    joined


    let get_by_label prog label =
      let is_none opt = match opt with | Some x -> false | None -> true in
      let force_get opt = match opt with | Some x -> x | None -> failwith "Optional is None" in
      let rec find_by_label label stmt =
        if (get_label stmt == label) then Some stmt
        else (match stmt with
        | ExtSeq (_, s1, s2) -> let res1 = find_by_label label s1 in
                                if (is_none res1) then find_by_label label s2 else res1
        | ExtIf (_, _, s1, s2) -> let res1 = find_by_label label s1 in
                                  if (is_none res1) then find_by_label label s2 else res1
        | ExtWhile (_, _, s) -> find_by_label label s
        | ExtRepeatUntil (_, cond, s) -> find_by_label label s
        | _ -> None) in
      force_get (find_by_label label prog)

    let get_successors prog label = let edges = SetInt2.filter (fun (l_from, _) -> l_from == label) (get_flow prog) in
                                    SetInt.of_list (List.map snd (SetInt2.elements edges))
                                    
    let get_predecessors prog label = let edges = SetInt2.filter (fun (_, l_to) -> l_to == label) (get_flow prog) in
                                      SetInt.of_list (List.map fst (SetInt2.elements edges))

    let depend_on x prog = map_build_set (SetExpr.empty) (SetExpr.union) (get_dependent_subexprs x) (SetExpr.elements (prog_exprs prog))
    
    let kills stmt prog = match stmt with
        | ExtSeq _ -> failwith ("Should not be called on seq statements")
        | ExtIf _ -> SetExpr.empty
        | ExtWhile _ -> SetExpr.empty
        | ExtRepeatUntil _ -> SetExpr.empty
        | ExtRead (_, x) -> depend_on x prog
        | ExtWrite _ -> SetExpr.empty
        | ExtAssign (_, x, _) -> depend_on x prog
        | ExtSkip _ -> SetExpr.empty

    let reverse flow = List.map (fun (x, y) -> (y, x)) flow

    let inter_unit prog = prog_exprs prog
    let inter_join prog (sets: 'SetExpr list) = List.fold_left (fun acc set -> SetExpr.inter acc set) (inter_unit prog) sets
    let inter_leq_reversed x y = SetExpr.subset y x (* whole set is the smallest one*)

end

module Solver = struct
  open ExtStmt
  open AnalysisGeneral
  let solve (flow: (int * int) list) join_fun leq_fun transfer_fun border_labels border_value unit_value =
    let labels = List.flatten (List.map (fun (x, y) -> [x; y]) flow) in

    let get_successors_edges label = List.filter (fun (l_from, _) -> l_from == label) flow in

    let iterate (edges, cur_results) = match edges with
      | [] -> (edges, cur_results)
      | (label_from, label_to) :: rest ->
        let new_result = transfer_fun label_from (cur_results label_from) in
        let old_target_result = cur_results label_to in
        if (not (leq_fun new_result old_target_result))
        then
          let new_target_result = join_fun [old_target_result; new_result] in
          let new_results = Expr.update label_to new_target_result cur_results in
          let new_edges = (get_successors_edges label_to) @ rest in
          (new_edges, new_results)
        else
          (rest, cur_results) in

    let rec iterate_until_convergence state =
        let (new_edges, new_analysis as new_state) = iterate state in
        (if (new_edges == [])
        then state else (iterate_until_convergence new_state)) in

    let set_initial_result label = if (List.mem label border_labels) then border_value else unit_value in
    let initial_results = List.fold_left (fun cur_fun lbl -> Expr.update lbl (set_initial_result lbl) cur_fun)
                                         (fun lbl -> unit_value) labels in

    let (_, analysis_entry) = iterate_until_convergence (flow, initial_results) in
    let analysis_exit label = transfer_fun label (analysis_entry label) in
    (analysis_entry, analysis_exit)

end

module VB' = struct
    open AnalysisGeneral
    open ExtStmt
    open Solver

    let vb_kills prog (label: int) = kills (get_by_label prog label) prog
    let vb_gens prog (label: int) = match (get_by_label prog label) with
        | ExtSeq _ -> failwith ("Should not be called on seq statements")
        | ExtIf (_, cond, _, _) -> get_all_subexprs cond
        | ExtWhile (_, cond, _) -> get_all_subexprs cond
        | ExtRepeatUntil (_, cond, _) -> get_all_subexprs cond
        | ExtRead (_, x) -> SetExpr.empty
        | ExtWrite (_, e) -> get_all_subexprs e
        | ExtAssign (_, _, e) -> get_all_subexprs e
        | ExtSkip _ -> SetExpr.empty

    let vb_transfer prog label exprs = SetExpr.union (SetExpr.diff exprs (vb_kills prog label)) (vb_gens prog label)

    let vb_solver prog = solve (reverse (SetInt2.elements (get_flow prog))) (inter_join prog) inter_leq_reversed
                               (vb_transfer prog) (SetInt.elements (get_finish_labels prog)) (SetExpr.empty) (inter_unit prog)
end

module AE' = struct
    open AnalysisGeneral
    open ExtStmt
    open Solver

    let ae_kills prog (label: int) = kills (get_by_label prog label) prog
    let ae_gens prog (label: int) = match (get_by_label prog label) with
        | ExtSeq _ -> failwith ("Should not be called on seq statements")
        | ExtIf (_, cond, _, _) -> get_all_subexprs cond
        | ExtWhile (_, cond, _) -> get_all_subexprs cond
        | ExtRepeatUntil (_, cond, _) -> get_all_subexprs cond
        | ExtRead (_, x) -> SetExpr.empty
        | ExtWrite (_, e) -> get_all_subexprs e
        | ExtAssign (_, x, e) -> SetExpr.diff (get_all_subexprs e) (depend_on x prog)
        | ExtSkip _ -> SetExpr.empty

    let ae_transfer prog label exprs = SetExpr.union (SetExpr.diff exprs (ae_kills prog label)) (ae_gens prog label)

    let ae_solver prog = solve (SetInt2.elements (get_flow prog)) (inter_join prog) inter_leq_reversed
                               (ae_transfer prog) [get_init_label prog] (SetExpr.empty) (inter_unit prog)
end

(*module PRE = struct*)
(*    open AnalysisGeneral*)
(*    open ExtStmt*)

(*    let (vb_entry, _) = VB.analyze_vb prog in*)
(*    let (_, ae_exit) = AE.analyze_ae prog in*)
(*    let downsafe label =  vb_entry label in*)
(*    let upsafe label = ae_exit label in*)
(*    let cannot_use label = kills (get_by_label prog label) prog || (! ())*)

(*    let earliest prog expr label = downsafe label &&*)
(*end*)

let describe analyzer label =
  let on_entry, on_exit = analyzer in
  Printf.sprintf "On entry: %s # On exit: %s: " (show_list (on_entry label)) (show_list (on_exit label))


let optimize orig_prog =
  let prog = ExtStmt.enhance orig_prog in
  let (vb_exit, vb_entry) = VB'.vb_solver prog in
  let (ae_entry, ae_exit) = AE'.ae_solver prog in
  Printf.eprintf "flow: \n%s\n" (show_flow (SetInt2.elements (AnalysisGeneral.get_flow prog)));
  Printf.eprintf "program: \n%s\n" (ExtStmt.tostring prog  (fun lbl -> describe (vb_entry, vb_exit) lbl));
  (*  Printf.eprintf "program: \n%s\n" (ExtStmt.tostring prog  (fun lbl -> describe (ae_entry, ae_exit) lbl));*)

  orig_prog

