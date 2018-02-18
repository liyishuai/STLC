Require Import Omega.
Require Import Equalities.

Open Scope nat_scope.

Definition var := nat.

Inductive typ :=
  TUnit
| Tarr (arg res : typ).

Definition env := var -> option typ.

Inductive exp :=
  EVar (v : var)
| EAbs (v : var) (vty : typ) (body : exp)
| EApp (fn arg : exp)
| ETrue | EFalse
| EIf (cond btrue bfalse : exp).

Definition is_value (e : exp) : bool :=
  match e with
  | EAbs _ _ _ => true
  | ETrue      => true
  | EFalse     => true
  | _          => false
  end.

Inductive value : exp -> Prop :=
  value_abs   : forall v vty body, value (EAbs v vty body)
| value_true  : value ETrue
| value_false : value EFalse.

Hint Constructors value.

Lemma value_is_value : forall e, value e <-> is_value e = true.
Proof with auto.
  split;
  induction e;
  simpl;
  intro H;
  inversion H;
  subst...
Qed.

Reserved Notation "'[' x ':=' e ']' e'" (at level 20).

Fixpoint subst (x : var) (e e' : exp) : exp :=
  match e' with
  | EVar x'      => if x =? x' then e else e'
  | EAbs x' t e1 => EAbs x' t (if x =? x' then e1 else [x:=e]e1)
  | EApp e1 e2   => EApp ([x:=e]e1) ([x:=e]e2)
  | EIf e1 e2 e3 => EIf ([x:=e]e1) ([x:=e]e2) ([x:=e]e3)
  | _            => e'
  end
where "'[' x ':=' e ']' e'" := (subst x e e').

Inductive substi (x : var) (e : exp) : exp -> exp -> Prop :=
  s_var1  : substi x e (EVar x) e
| s_var2  : forall x', x <> x' -> substi x e (EVar x') (EVar x')
| s_abs1  : forall t e1, substi x e (EAbs x t e1) (EAbs x t e1)
| s_abs2  : forall x', x <> x' -> forall e1 e1',
      substi x e e1 e1' -> forall t,
        substi x e (EAbs x' t e1) (EAbs x' t e1')
| s_app   : forall e1 e1', substi x e e1 e1' -> forall e2 e2',
      substi x e e2 e2' ->
      substi x e (EApp e1 e2) (EApp e1' e2')
| s_true  : substi x e ETrue  ETrue
| s_false : substi x e EFalse EFalse
| s_if    : forall e1 e1', substi x e e1 e1' -> forall e2 e2',
      substi x e e2 e2' -> forall e3 e3',
        substi x e e3 e3' ->
        substi x e (EIf e1 e2 e3) (EIf e1' e2' e3').

Hint Constructors substi.

Lemma substi_subst : forall x e e' e'', substi x e e' e'' <-> [x:=e]e' = e''.
Proof with auto.
  split.
  - intro H;
    induction H;
    subst;
    simpl;
    try rewrite Nat.eqb_refl;
    try (apply Nat.eqb_neq in H; rewrite H)...
  - generalize dependent e''.
    induction e';
    intros;
    unfold subst in H;
    subst; fold subst in *;
      try (destruct (Nat.eq_dec x v);
           [ subst; rewrite Nat.eqb_refl |
             replace (x =? v) with false in *; simpl in * ]; auto;
           symmetry; apply Nat.eqb_neq)...
Qed.

Fixpoint step (e : exp) : option exp :=
  match e with
  | EApp e1 e2 =>
    if is_value e1
    then if is_value e2
         then match e1 with
              | EAbs x t e1' => Some ([x:=e2]e1')
              | _            => None
              end
         else match step e2 with
              | Some e2' => Some (EApp e1 e2')
              | None     => None
              end
    else match step e1 with
         | Some e1' => Some (EApp e1' e2)
         | None     => None
         end
  | EIf e1 e2 e3 =>
    if is_value e1
    then match e1 with
         | ETrue  => Some e2
         | EFalse => Some e3
         | _      => None
         end
    else match step e1 with
         | Some e1' => Some (EIf e1' e2 e3)
         | None     => None
         end
  | _ => None
  end.

Lemma step_not_value : forall e e', step e = Some e' -> is_value e = false.
Proof with auto.
  destruct e; try (intros; inversion H)...
Qed.

Lemma value_not_step : forall e, is_value e = true -> step e = None.
Proof with auto.
  intros.
  destruct (step e) eqn:Hstep...
  apply step_not_value in Hstep.
  rewrite Hstep in H.
  inversion H.
Qed.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive stepR : exp -> exp -> Prop :=
  ST_AppAbs  : forall e2, value e2 -> forall x t e1,
      EApp (EAbs x t e1) e2 ==> [x:=e2]e1
| ST_App1    : forall e1 e1', e1 ==> e1' -> forall e2,
      EApp e1 e2 ==> EApp e1' e2
| ST_App2    : forall e1, value e1 -> forall e2 e2',
      e2 ==> e2' ->
      EApp e1 e2 ==> EApp e1 e2'
| ST_IfTrue  : forall e1 e2, EIf ETrue e1 e2 ==> e1
| ST_IfFalse : forall e1 e2, EIf EFalse e1 e2 ==> e2
| ST_If      : forall e1 e1', e1 ==> e1' -> forall e2 e3,
      EIf e1 e2 e3 ==> EIf e1' e2 e3
where "e1 '==>' e2" := (stepR e1 e2).

Hint Constructors stepR.

Lemma stepR_step : forall e1 e2, stepR e1 e2 <-> step e1 = Some e2.
Proof with simpl in *; eauto.
  split.
  - intro H.
    induction H;
    simpl;
    try (apply value_is_value in H; rewrite H);
    try erewrite step_not_value;
    try rewrite IHstepR...
  - generalize dependent e2.
    induction e1; intros; inversion H...
    + destruct (is_value e1_1) eqn:Hv1.
      * destruct (is_value e1_2) eqn:Hv2.
        ** destruct e1_1; inversion Hv1; inversion H; subst.
           constructor.
           apply value_is_value...
        ** destruct (step e1_2); inversion H.
           apply ST_App2...
           apply value_is_value...
      * destruct (step e1_1); inversion H...
    + destruct (is_value e1_1) eqn:Hv1.
      * destruct e1_1; inversion Hv1; inversion H...
      * destruct (step e1_1); inversion H...
Qed.

Fixpoint multistep_rec' n e : option exp :=
  match n with
  | 0    => None
  | S n' => match step e with
           | Some e' => multistep_rec' n' e'
           | None    => None
           end
  end.

Definition bigNumber : nat := 5000.

Definition multistep' : exp -> option exp :=
  multistep_rec' bigNumber.

Lemma multistep_rec'_None : forall n e, multistep_rec' n e = None.
Proof with auto.
  induction n...
  induction e; simpl...
  - destruct (is_value e1) eqn:Hv1.
    + destruct (is_value e2).
      * destruct e1; inversion Hv1...
      * destruct (step e2)...
    + destruct (step e1)...
  - destruct (is_value e1) eqn:Hv1.
    + destruct e1; inversion Hv1...
    + destruct (step e1)...
Qed.

Definition multistep'_None : forall e, multistep' e = None :=
  multistep_rec'_None bigNumber.

Fixpoint multistep_rec n e : option exp :=
  if is_value e then Some e
  else
    match n with
    | 0    => Some e
    | S n' => match step e with
             | None    => None
             | Some e' => multistep_rec n' e'
             end
    end.

Definition multistep : exp -> option exp :=
  multistep_rec bigNumber.

Inductive multi {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  multi_refl : forall x, multi R x x
| multi_step : forall x y z,
    R x y ->
    multi R y z ->
    multi R x z.

Hint Constructors multi.

Definition multistepR : exp -> exp -> Prop := multi stepR.

Lemma multistepR_multistep_rec : forall e e', multistepR e e' <-> exists n, multistep_rec n e = Some e'.
Proof with simpl in *; auto.
  split.
  - intros.
    induction H...
    + exists 0.
      simpl.
      destruct (is_value x)...
    + destruct IHmulti.
      exists (S x0).
      simpl.
      replace (is_value x) with false;
      apply stepR_step in H;
      [ | apply step_not_value in H];
      rewrite H...
  - intros [n H].
    generalize dependent e.
    generalize dependent e'.
    induction n; intros.
    + inversion H.
      destruct (is_value e); inversion H1; constructor.
    + inversion H; subst.
      destruct (is_value e); inversion H1; subst; try constructor...
      destruct (step e) eqn:Hstep; inversion H1.
      apply stepR_step in Hstep.
      apply multi_step with e0...
      apply IHn.
      destruct (is_value e); inversion H; subst...
Qed.

Lemma multistep_multistepR : forall e e', multistep e = Some e' -> multistepR e e'.
Proof with eauto.
  intros.
  apply multistepR_multistep_rec...
Qed.
