open Parser_plaf.Ast
open Parser_plaf.Parser
open Ds

(** [eval_expr e] evaluates expression [e] *)
let rec eval_expr : expr -> exp_val ea_result =
  fun e ->
  match e with
  | Int(n) ->
    return (NumVal n)
  | Var(id) ->
    apply_env id
  | Add(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1+n2))
  | Sub(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1-n2))
  | Mul(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    return (NumVal (n1*n2))
  | Div(e1,e2) ->
    eval_expr e1 >>=
    int_of_numVal >>= fun n1 ->
    eval_expr e2 >>=
    int_of_numVal >>= fun n2 ->
    if n2==0
    then error "Division by zero"
    else return (NumVal (n1/n2))
  | Let(id,def,body) ->
    eval_expr def >>= 
    extend_env id >>+
    eval_expr body 
  | ITE(e1,e2,e3) ->
    eval_expr e1 >>=
    bool_of_boolVal >>= fun b ->
    if b 
    then eval_expr e2
    else eval_expr e3
  | IsZero(e) ->
    eval_expr e >>=
    int_of_numVal >>= fun n ->
    return (BoolVal (n = 0))
  | Pair(e1,e2) ->
    eval_expr e1 >>= fun ev1 ->
    eval_expr e2 >>= fun ev2 ->
    return (PairVal(ev1,ev2))
  | Fst(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (l,_) ->
    return l
  | Snd(e) ->
    eval_expr e >>=
    pair_of_pairVal >>= fun (_,r) ->
    return r
  | Debug(_e) ->
    string_of_env >>= fun str ->
    print_endline str; 
    error "Debug called"
  | IsEmpty(e) -> 
    eval_expr e >>=
    tree_of_treeVal >>= fun tree ->
    return (BoolVal (tree = Empty))
  | EmptyTree(_t) -> return (TreeVal Empty)
  | Node(e1,e2,e3) -> 
    eval_expr e1 >>= int_of_numVal >>= fun ev1 ->
    eval_expr e2 >>= tree_of_treeVal >>= fun ev2 ->
    eval_expr e3 >>= tree_of_treeVal >>= fun ev3 ->
    return (TreeVal (Node (NumVal ev1, ev2, ev3)))
  | CaseT(e1,e2,id1,id2,id3,e3) ->
    (eval_expr e1 >>= tree_of_treeVal >>= fun t1 ->
      match t1 with
      | Empty -> eval_expr e2
      | Node (a, l, r) -> extend_env id1 a >>+
      extend_env id2 (TreeVal l) >>+
      extend_env id3 (TreeVal r) >>+
      eval_expr e3)
  | Record(fs) -> 
    let rec record_helper fs used_ids =
      match fs with
      | [] -> return []
      | (id, (_, e))::t ->
        if find_id id used_ids then error ("Record: duplicate fields")
        else
          eval_expr e >>= fun ev ->
          extend_env id ev >>+
          record_helper t (id::used_ids) >>= fun fs_t ->
          return ((id, ev)::fs_t)
    in record_helper fs [] >>= fun processed_fields ->
    return (RecordVal processed_fields)
  | Proj(e,id) -> 
    eval_expr e >>= record_of_recordVal >>= fun r -> record_get id r
  | _ -> failwith "Not implemented yet!"

(** [eval_prog e] evaluates program [e] *)
let eval_prog (AProg(_,e)) =
  eval_expr e

(** [interp s] parses [s] and then evaluates it *)
let interp (e:string) : exp_val result =
  let c = e |> parse |> eval_prog
  in run c