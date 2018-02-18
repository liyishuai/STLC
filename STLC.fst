(*
TODO:
multistepper (actually converges but F* might not be able to prove it and mark as div)
bigstep (actually converges but F* might not be able to prove it and mark as div)
prove multistepper = bigstep
*)

(* Try to prove termination for multistep and bigstep by providing a proper terminating metric on line 53 for step*)
(*
TODO: (decreases)
the evaluation sequences for t1 and t2 or t3 are strictly shorter than the given evaluation sequence.
e.g. if t1 then t2 else t3  →∗ v
(And similarly for the other term constructors.)
*)

module STLC

(* change nat to general a *)
type var = nat

type typ: Type =
  | TUnit : typ
  | TArr  : arg : typ -> res : typ -> typ

type env = var(* int *) -> Tot (option typ)

type exp: Type =
  | EVar : v:var -> exp
  | EAbs : v:var -> vty:typ -> body:exp -> exp
  | EApp : fn:exp -> arg:exp -> exp
  | ETrue : exp
  | EFalse : exp
  | EIf : cond:exp -> btrue:exp -> bfalse:exp -> exp

val is_value: exp -> Tot bool
let is_value e = match e with
    | EAbs _ _ _
    | ETrue
    | EFalse     -> true
    | _          -> false

val subst: var(* int *) -> exp -> exp -> Tot exp
let rec subst x e e' = match e' with
  | EVar x' -> if x = x' then e else e'
  | EAbs x' t e1 -> EAbs x' t (if x = x' then e1 else (subst x e e1))
  | EApp e1 e2 -> EApp (subst x e e1) (subst x e e2)
  | ETrue -> ETrue
  | EFalse -> EFalse
  | EIf e1 e2 e3 -> EIf (subst x e e1) (subst x e e2) (subst x e e3)

val step: exp -> Tot (option exp)
(*
TODO: (decreases)
the evaluation sequences for t1 and t2 or t3 are strictly shorter than the given evaluation sequence.
e.g. if t1 then t2 else t3  →∗ v
(And similarly for the other term constructors.)
*)
let rec step e = match e with
  | EApp e1 e2 ->
    if is_value e1
    then
      if is_value e2
      then match e1 with
        | EAbs x t e1' -> Some (subst x e2 e1')
        | _ -> None
      else match (step e2) with
        | Some e2' -> Some (EApp e1 e2')
        | None -> None
    else (match (step e1) with
      | Some e1' -> Some (EApp e1' e2)
      | None -> None)
  | EIf e1 e2 e3 ->
    if is_value e1
    then match e1 with
        | ETrue  -> Some e2
        | EFalse -> Some e3
        | _ -> None
    else (match (step e1) with
      | Some e1' -> Some (EIf e1' e2 e3)
      | None -> None)
  | _ -> None

(* val multistep: e:exp -> Tot (t:(option exp){Some? t ==> is_value (Some?.v t)}) *)
val multistep: e:exp -> Dv (t:(option exp){Some? t ==> is_value (Some?.v t)})
let rec multistep e = match (step e) with
  | Some e' -> multistep e'
  | None -> None

(* val bigstep: e:exp -> Tot (t:(option exp){Some? t ==> is_value (Some?.v t)}) *)
val bigstep: exp -> Dv (t:option exp{Some? t ==> is_value (Some?.v t)})
let rec bigstep e = match e with
  | EApp e1 e2 ->
    if is_value e1
    then match e1 with
      | EAbs x t e1' ->
        if is_value e2
        then bigstep (subst x e2 e1')
        else (
          match bigstep e2 with
            | Some v2 ->
              if is_value v2
              then bigstep (subst x v2 e1')
              else None
            | None -> None)
      | _ -> None
    else (match bigstep e1 with
      | Some v1 -> (
        match v1 with
          | EAbs x t e1' ->
            if is_value e2
            then bigstep (subst x e2 e1')
            else (match bigstep e2 with
              | Some v2 ->
                if is_value v2
                then bigstep (subst x v2 e1')
                else None
              | None -> None)
          | _ -> None
        )
      | _ -> None)
  | EIf e1 e2 e3 ->
    if is_value e1
    then match e1 with
        | ETrue  -> bigstep e2
        | EFalse -> bigstep e3
        | _ -> None
    else (match (bigstep e1) with
      | Some v1 -> (match v1 with
        | ETrue -> bigstep e2
        | EFalse -> bigstep e3
        | _ -> None)
      | None -> None)
  | _ -> None
