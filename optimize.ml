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
  let hash : (string, bool) Hashtbl.t = Hashtbl.create 0 in
      (* is the given expression pure or not?
      Also, update ans with any bindings you encounter. *)
  let rec helpA ae =
      match ae with
      | ALet(name, ce, ae, _) ->
          Hashtbl.add hash name (helpC ce);
          helpA ae
      | ASeq(ce, rest, _) ->
          helpC ce && helpA rest
      | ACExpr ce -> helpC ce
      | _ -> failwith "Implement this"
  and helpC ce =
      match ce with
      | CIf(con, thn, els, _) ->
          helpI con && helpA thn && helpA els
      | CPrim1(_, e, _) ->
          helpI e
      | CPrim2(_, e1, e2, _) ->
          helpI e2 && helpI e2
      | CApp(func, args, _) ->
          helpI func && List.for_all helpI args
      | CTuple(ls, _) ->
          (*List.for_all helpI ls*)
          false
      | CGetItem(tup, idx, _) ->
          (*helpI tup && helpI idx*)
          false
      | CSetItem(tup, idx, value, _) ->
          (*Hashtbl.replace hash (nameof tup) false;*)
          false; (*?*)
      | CLambda(args, body, _) ->
          List.iter (fun x -> Hashtbl.add hash x true) args;
          let ans = helpA body in
          List.iter (fun x -> Hashtbl.remove hash x) args;
          ans
      | CImmExpr e -> helpI e
  and helpI (imm : tag immexpr) : bool =
      match imm with
      | ImmNum _ -> true
      | ImmBool _ -> true
      | ImmId(x, _) -> Hashtbl.find hash x
  and nameof imm =
      match imm with
      | ImmId(x, _) -> x
      | _ -> failwith "Impossible"
  in ignore(helpA prog); hash

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
  in match simple with
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

let rec untagA ae =
    match ae with
    | ALet(name, ce, ae, _) -> ALet(name, untagC ce, untagA ae, ())
    | ALetRec(ls, ae, _) -> ALetRec(List.map (fun (name, ce) -> (name, untagC ce)) ls, untagA ae, ())
    | ASeq(ce, rest, _) -> ASeq(untagC ce, untagA rest, ())
    | ACExpr ce -> ACExpr(untagC ce)
and untagC ce =
    match ce with
    | CPrim1(op, e, _) -> CPrim1(op, untagI e, ())
    | CPrim2(op, e1, e2, _) -> CPrim2(op, untagI e1, untagI e2, ())
    | CIf(cond, thn, els, _) -> CIf(untagI cond, untagA thn, untagA els, ())
    | CTuple(vals, _) -> CTuple(List.map untagI vals, ())
    | CGetItem(tup, idx, _) -> CGetItem(untagI tup, untagI idx, ())
    | CSetItem(tup, idx, rhs, _) -> CSetItem(untagI tup, untagI idx, untagI rhs, ())
    | CApp(func, args, _) -> CApp(untagI func, List.map untagI args, ())
    | CLambda(args, body, _) -> CLambda(args, untagA body, ())
    | CImmExpr i -> CImmExpr (untagI i)
and untagI ie =
    match ie with
    | ImmId(x, _) -> ImmId(x, ())
    | ImmNum(n, _) -> ImmNum(n, ())
    | ImmBool(b, _) -> ImmBool(b, ())

let const_fold (prog : tag aprogram) : (unit aprogram) =
    let try_add name ce ls = match ce with
        | CImmExpr imm -> (name,imm)::ls
        | _ -> ls in
    let get_num imm = match imm with
        | ImmNum(x, _) -> x
        | _ -> failwith "Impossible: get_num" in
    let get_bool imm = match imm with
        | ImmBool(x, _) -> x
        | _ -> failwith "Impossible: get_bool" in
    let is_num imm = match imm with
        | ImmNum _ -> true
        | ImmBool _ -> false
        | _ -> failwith "Impossible: is_num" in
    let rec helpA ae env =
        match ae with
        | ALet(name, ce, ae, _) ->
            let ans = helpC ce env in
            ALet(name, ans, helpA ae (try_add name ans env), ())
        | ALetRec(ls, ae, _) ->
            ALetRec(List.map (fun (name, ce) -> (name, helpC ce env)) ls, helpA ae env, ())
        | ASeq(ce, rest, _) ->
            ASeq(helpC ce env, helpA rest env, ())
        | ACExpr ce ->
            ACExpr(helpC ce env)
    and helpC ce env =
        match ce with
        | CPrim1(op, e, _) ->
            (try (match e with
                | ImmId(name, _) ->
                     helpC (CPrim1(op, List.assoc name env, ())) env
                | ImmId _ -> ce
                | _ -> (match op with
                    | Add1 -> CImmExpr(ImmNum(((get_num e) + 1), ()))
                    | Sub1 -> CImmExpr(ImmNum(((get_num e) - 1), ()))
                    | Not -> CImmExpr(ImmBool(not(get_bool e), ()))
                    | IsNum -> CImmExpr(ImmBool(is_num e, ()))
                    | IsBool -> CImmExpr(ImmBool(not(is_num e), ()))
                    | _ -> ce)) with
            | _ -> ce)
        | CPrim2(op, e1, e2, _) ->
            (try (match e1, e2 with
                | ImmId(name, _), _ -> helpC (CPrim2(op, List.assoc name env, e2, ())) env
                | _, ImmId(name, _) -> helpC (CPrim2(op, e1, List.assoc name env, ())) env
                | _ -> (match op with
                    | Plus -> CImmExpr(ImmNum((get_num e1) + (get_num e2), ()))
                    | Minus -> CImmExpr(ImmNum((get_num e1) - (get_num e2), ()))
                    | Times -> CImmExpr(ImmNum((get_num e1) * (get_num e2), ()))
                    | Less -> CImmExpr(ImmBool((get_num e1) < (get_num e2), ()))
                    | Greater -> CImmExpr(ImmBool((get_num e1) > (get_num e2), ()))
                    | LessEq -> CImmExpr(ImmBool((get_num e1) <= (get_num e2), ()))
                    | GreaterEq -> CImmExpr(ImmBool((get_num e1) >= (get_num e2), ()))
                    | Eq -> CImmExpr(ImmBool((get_num e1) = (get_num e2), ()))
                    | And -> CImmExpr(ImmBool((get_bool e1) && (get_bool e2), ()))
                    | Or -> CImmExpr(ImmBool((get_bool e1) || (get_bool e2), ())))) with
            | _ -> ce)
        | CIf(con, thn, els, _) ->
            CIf(helpI con env, helpA thn env, helpA els env, ())
        | CApp(func, args, _) ->
            CApp(helpI func env, List.map (fun x -> helpI x env) args, ())
        | CTuple(ls, _) ->
            CTuple(List.map (fun x -> helpI x env) ls, ())
        | CGetItem(tup, idx, _) ->
            CGetItem(helpI tup env, helpI idx env, ())
        | CSetItem(tup, idx, rhs, _) ->
            CSetItem(helpI tup env, helpI idx env, helpI rhs env, ())
        | CLambda(args, body, _) ->
            CLambda(args, helpA body env, ())
        | CImmExpr i ->
            CImmExpr(helpI i env)
    and helpI ie env =
        match ie with
        | ImmId(name, _) when List.mem_assoc name env ->
            List.assoc name env
        | _ -> ie in
    helpA (untagA prog) []

let cse (prog : tag aprogram) : unit aprogram =
    let rec helpA e eql =
        match e with
        | ALet(name, ce, ae, _) ->
            (* TODO: Interaction with purity *)
            let new_ce = helpC ce eql in
            (match cexpr_to_simple_opt new_ce with
            | Some sex -> ALet(name, new_ce, helpA ae ((sex, name)::eql), ())
            | None -> ALet(name, new_ce, helpA ae eql, ()))
        | ALetRec(ls, ae, _) ->
            ALetRec(List.map (fun (name, body) -> name, helpC body eql) ls, helpA ae eql, ())
        | ASeq(ce, rs, _) ->
            let new_ce = helpC ce eql in
            let new_rs = helpA rs eql in
            ASeq(new_ce, new_rs, ())
        | ACExpr ce ->
            ACExpr(helpC ce eql)
    and helpC e eql =
        match e with
        | CPrim1 _ | CPrim2 _ | CApp _ | CImmExpr _ ->
            (match cexpr_to_simple_opt e with
            | Some sex when List.mem_assoc sex eql ->
                CImmExpr(ImmId(List.assoc sex eql, ()))
            | _ -> (match e with
                | CPrim1(op, i, _) ->
                    let sex = imm_to_simple i in
                    if List.mem_assoc sex eql then
                        CPrim1(op, ImmId(List.assoc sex eql, ()), ())
                    else untagC e
                | CPrim2(op, e1, e2, _) ->
                    let sex1 = imm_to_simple e1 in
                    let sex2 = imm_to_simple e2 in
                    if List.mem_assoc sex1 eql && List.mem_assoc sex2 eql then
                        CPrim2(op, ImmId(List.assoc sex1 eql, ()), ImmId(List.assoc sex1 eql, ()), ())
                    else if List.mem_assoc sex1 eql then
                        CPrim2(op, ImmId(List.assoc sex1 eql, ()), untagI e2, ())
                    else if List.mem_assoc sex2 eql then
                        CPrim2(op, untagI e1, ImmId(List.assoc sex1 eql, ()), ())
                    else untagC e
                | CApp(func, args, _) ->
                    let sex_ls = List.map
                        (fun x -> let sex = imm_to_simple x in
                            if List.mem_assoc sex eql then
                                ImmId(List.assoc sex eql, ())
                            else untagI x)
                        args in
                    CApp(untagI func, sex_ls, ())
                | CImmExpr i ->
                    let sex = imm_to_simple i in
                    if List.mem_assoc sex eql then
                        CImmExpr(ImmId(List.assoc sex eql, ()))
                    else untagC e
                | _ -> failwith "Impossible case"))
        | CTuple _ | CGetItem _ | CSetItem _ ->
            (* TODO: Add more sophisticated optimization? *)
            untagC e
        | CIf(cond, thn, els, _) ->
            CIf(untagI cond, helpA thn eql, helpA els eql, ())
        | CLambda(args, body, _) ->
            CLambda(args, helpA body eql, ()) in
    helpA prog []

let dae (prog : tag aprogram) : unit aprogram =
    (*let purity = purity_env prog in*)
    let rec helpA e =
        match e with
        | ALet(name, ce, ae, _) ->
            (* TODO: Interaction with purity *)
            let (new_ae, used_ls) = helpA ae in
            if List.mem name used_ls then
                let new_ce, used_ce = helpC ce in
                ALet(name, new_ce, new_ae, ()), used_ce @ used_ls
            else new_ae, used_ls
        | ALetRec(ls, ae, _) ->
            (* TODO: Eliminate dead mutually-recursive functions *)
            let new_ae, used_ae = helpA ae in
            let used_ls = List.flatten (List.map (fun x -> snd (helpC (snd x))) ls) in
            let cleanup = List.flatten (List.map
                (fun x -> if List.mem (fst x) (used_ae @ used_ls) then [x] else [] ) ls) in
            let new_temp = List.map (fun (f, b) -> let (n, ls) = helpC b in ((f, n), ls)) cleanup in
            let new_ls = List.map fst new_temp in
            let used_new = List.flatten (List.map snd new_temp) in
            ALetRec(new_ls, new_ae, ()), used_ae @ used_new
        | ASeq(ce, rest, _) ->
            let new_ce, used_ce = helpC ce in
            let new_rest, used_rest = helpA rest in
            ASeq(new_ce, new_rest, ()), used_ce @ used_rest
        | ACExpr ce ->
            let new_ce, used_ce = helpC ce in
            ACExpr(new_ce), used_ce
     and helpC ce =
        match ce with
        | CPrim1(op, e, _) ->
            (untagC ce, helpI e)
        | CPrim2(op, e1, e2, _) ->
            (untagC ce, helpI e1 @ helpI e2)
        | CIf(cond, thn, els, _) ->
            let new_thn, used_thn = helpA thn in
            let new_els, used_els = helpA els in
            (CIf(untagI cond, new_thn, new_els, ()), helpI cond @ used_thn @ used_els)
        | CTuple(vals, _) ->
            (untagC ce, List.flatten (List.map helpI vals))
        | CGetItem(tup, idx, _) ->
            (untagC ce, helpI tup @ helpI idx)
        | CSetItem(tup, idx, rhs, _) ->
            untagC ce, helpI tup @ helpI idx @ helpI rhs
        | CApp(name, args, _) ->
            untagC ce, helpI name @ (List.flatten (List.map helpI args))
        | CLambda(ls, body, _) ->
            let new_body, used_body = helpA body in
            CLambda(ls, new_body, ()), used_body
        | CImmExpr i ->
            untagC ce, helpI i
    and helpI i =
        match i with
        | ImmId(x, _) -> [x]
        | _ -> [] in
    fst (helpA prog)

let optimize prog =
    let pass prog =
        let const_prog = atag (const_fold prog) in
        let dae_prog = atag (dae const_prog) in
        let cse_prog = atag (cse dae_prog) in
        (*printf "Const/tagged:\n%s\n" (string_of_aprogram const_prog);*)
        (*printf "DAE/tagged:\n%s\n" (string_of_aprogram dae_prog);*)
        (*printf "CSE/tagged:\n%s\n" (string_of_aprogram cse_prog);*)
        cse_prog in
    let opt = pass(pass(pass(prog))) in
    (*printf "Prog:\n%s\n" (string_of_aprogram opt);*)
    opt;
