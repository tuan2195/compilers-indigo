open Types
open Printf
open Instruction
open Expr
open Pretty

let rec rm_dup ls =
    let rec rm_from ls x =
        (match ls with
        | [] -> []
        | n::rs when n = x -> rm_from rs x
        | _ -> List.hd ls :: rm_from (List.tl ls) x ) in
    match ls with
    | [] -> []
    | x::rs ->
        let new_ls = rm_from rs x in
        x::rm_dup new_ls

let rec free_a ae env =
    match ae with
    | ALet(name, expr, body, _) ->
        free_c expr env @ free_a body (name::env)
    | ALetRec(expr_ls, body, _) ->
        free_a body (env @ (List.map fst expr_ls))
    | ASeq(expr, rest, _) ->
        free_c expr env @ free_a rest env
    | ACExpr(e) ->
        free_c e env
and free_c ce env =
    match ce with
    | CIf(con, thn, els, _) ->
        free_i con env @
        free_a thn env @
        free_a els env
    | CPrim1(_, e, _) ->
        free_i e env
    | CPrim2(_, e1, e2, _) ->
        free_i e1 env @
        free_i e2 env
    | CApp(func, args, _) ->
        free_i func env @
        List.flatten (List.map (fun x -> free_i x env) args)
    | CTuple(args, _) ->
        List.flatten (List.map (fun x -> free_i x env) args)
    | CGetItem(tup, idx, _) ->
        free_i tup env @ free_i idx env
    | CLambda(args, expr, _) ->
        free_a expr args
    | CImmExpr(i) ->
        free_i i env
    | CSetItem(tup, idx, expr, _) ->
        free_i tup env @ free_i idx env @ free_i expr env
and free_i ie env =
    match ie with
    | ImmNum _ | ImmBool _ -> []
    | ImmId(x, _) ->
        (try ignore (List.find (fun s -> s = x) env); [] with Not_found -> [x])

let free_vars ae = rm_dup (free_a ae [])

(*Optimization*)

let strip ls = ls
    (*match ls with*)
    (*| [] -> []*)
    (*| ILineComment(_)::rest -> strip rest*)
    (*| IInstrComment(i, _)::rest -> i::strip rest*)
    (*| i::rest -> i::strip rest*)

let peephole ls =
    let rec opt ls =
        match ls with
        | [] -> []
        | IMov(RegOffset(o1, b1), Reg(r1))::IMov(Reg(r2), RegOffset(o2, b2))::rest ->
            if o1 = o2 && b1 = b2 && r1 = r2 then
                (List.hd ls)::opt rest
            else
                (List.hd ls)::opt (List.tl ls)
        | what::rest ->
            what::opt rest in
    opt (strip ls)

let purity_env (prog : tag aprogram) : (string, bool) Hashtbl.t =
  let ans : (string, bool) Hashtbl.t = Hashtbl.create 0 in
  let rec helpA (aexp : tag aexpr) : bool =
      failwith "Implement this"
    (* is the given expression pure or not?
       Also, update ans with any bindings you encounter. *)
  and helpC (cexp : tag cexpr) : bool =
      failwith "Implement this"
  and helpI (imm : tag immexpr) : bool =
      failwith "Implement this"
  in
  ignore(helpA prog);
  ans


type simple_expr =
  | Id of string
  | Num of int
  | Bool of bool
  | Prim1 of prim1 * simple_expr
  | Prim2 of prim2 * simple_expr * simple_expr
  | App of simple_expr * simple_expr list

let rec string_of_simple s =
  match s with
  | Id s -> s
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Prim1(op, arg) -> sprintf "%s(%s)" (string_of_op1 op) (string_of_simple arg)
  | Prim2(op, left, right) -> sprintf "%s(%s, %s)" (string_of_op2 op) (string_of_simple left) (string_of_simple right)
  | App(f, args) -> sprintf "%s(%s)" (string_of_simple f) (ExtString.String.join ", " (List.map string_of_simple args))
;;
let rec simple_to_cexpr simple =
  let rec s_to_imm s =
    match s with
    | Id n -> ImmId(n, ())
    | Num n -> ImmNum(n, ())
    | Bool b -> ImmBool(b, ())
    | _ -> failwith "Impossible"
  in
  match simple with
  | Prim1(op, arg) -> CPrim1(op, s_to_imm arg, ())
  | Prim2(op, left, right) -> CPrim2(op, s_to_imm left, s_to_imm right, ())
  | App(f, args) -> CApp(s_to_imm f, List.map s_to_imm args, ())
  | _ -> CImmExpr (s_to_imm simple)
;;
let imm_to_simple i =
  match i with
  | ImmId(n, _) -> Id n
  | ImmNum(n, _) -> Num n
  | ImmBool(b, _) -> Bool b
;;
let cexpr_to_simple_opt cexp =
  match cexp with
  | CPrim1(op, arg, _) -> Some (Prim1(op, imm_to_simple arg))
  | CPrim2(op, left, right, _) -> Some (Prim2(op, imm_to_simple left, imm_to_simple right))
  | CApp(f, args, _) -> Some (App(imm_to_simple f, List.map imm_to_simple args))
  | CImmExpr i -> Some (imm_to_simple i)
  | _ -> None
;;

let const_fold (prog : tag aprogram) : unit aprogram =
      failwith "Implement this"


let cse (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
  (* This table maps arbitrary simple expressions to simpler ones
     that are equal to them: for example, "let x = a + b in" should map (a + b)
     to x.  You will likely need the generality of simple_expr for both the
     keys and the values of this table, but if you're careful, you might
     be able to simplify it to map simpl_exprs to strings. *)
  let equiv_exprs : (simple_expr, simple_expr) Hashtbl.t = Hashtbl.create 0 in
      failwith "Implement this"

let dae (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
      failwith "Implement this"

let optimize (prog : tag aprogram) (verbose : bool) : tag aprogram =
  let const_prog = atag (const_fold prog) in
  let cse_prog = atag (cse const_prog) in
  let dae_prog = atag (dae cse_prog) in
  (*(if verbose then begin*)
       (*printf "Const/tagged:\n%s\n" (string_of_aprogram const_prog ~-1);*)
       (*printf "CSE/tagged:\n%s\n" (string_of_aprogram cse_prog ~-1);*)
       (*printf "DAE/tagged:\n%s\n" (string_of_aprogram (atag dae_prog) ~-1)*)
     (*end*)
   (*else ());*)
  dae_prog
