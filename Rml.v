From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.reals.

Reserved Notation "x >>= f" (at level 40, left associativity).
Class Monad (M : Type -> Type) :=
  {
    unit : forall {A}, A -> M A;
    bind : forall {A B}, M A -> (A -> M B) -> M B
    where "x >>= f" := (bind x f);
    monad_law_unit_l : forall {A B} (a : A) (k : A -> M B), unit a >>= k = k a;
    monad_law_unit_r : forall {A} (x : M A), x >>= unit = x;
    monad_law_assoc : forall {A B C} (x : M A) (k : A -> M B) (h : B -> M C),
        x >>= (fun a => k a >>= h) = x >>= k >>= h
  }.
Notation "x >>= f" := (bind x f).
         
(* -------------------------------------------------------------------------------- *)

Definition continuation_monad_type := fun ZO A => (A -> ZO) -> ZO.
Instance continuation_monad {ZO} : Monad (continuation_monad_type ZO) :=
  {
    unit := fun {A} (x : A) (f : A -> ZO) => f x ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

(* -------------------------------------------------------------------------------- *)

Inductive Rml : Type :=
| Var : nat -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
(* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed : seq nat -> Rml -> Prop :=
| well_const : forall A c l, well_formed l (Const A c)
| well_var : forall x l, List.In x l -> well_formed l (Var x)
| well_let_stm : forall x e1 e2 l, well_formed l e1 -> well_formed (x :: l) e2 -> well_formed l (Let_stm x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

Inductive well_formed_empty : Rml -> Prop :=
| well : forall rml, well_formed nil rml -> well_formed_empty rml.

Example var_not_well_formed :
  forall n, well_formed_empty (Var n) -> False.
Proof.
  intros.
  inversion H ; subst ; clear H.
  inversion H0 ; subst.
  easy.
Qed.

Example var_in_let_well_formed :
  forall n rml, well_formed_empty rml -> well_formed_empty (Let_stm n rml (Var n)).
Proof.
  intros.
  apply well.
  apply well_let_stm.
  - inversion H ; subst ; clear H.
    apply H0.
  - apply well_var.
  - left.
    reflexivity.
Qed.  

Example var_not_in_let_well_formed :
  forall n1 n2 rml, n1 <> n2 -> well_formed_empty (Let_stm n1 rml (Var n2)) -> False.
Proof.
  intros.
  inversion H0 ; subst ; clear H0.
  inversion H1 ; subst ; clear H1.
  clear H4.
  inversion H6 ; subst ; clear H6.
  inversion H2.
  easy.
  easy.
Qed.  

(* -------------------------------------------------------------------------------- *)

Fixpoint replace_var_with_value (x : Rml) (index : nat) (value : Rml) : Rml :=
  match x with
  | Var n =>
    if n == index
    then value
    else x
  | Const A c => x
  | Let_stm n a b =>
    let new_value := replace_var_with_value a index value in
    if n == index
    then replace_var_with_value b index new_value
    else replace_var_with_value b index value
  | If_stm b m1 m2 =>
    let b' := replace_var_with_value b index value in
    let m1' := replace_var_with_value m1 index value in
    let m2' := replace_var_with_value m2 index value in
    If_stm b' m1' m2'
  | App_stm B e1 e2 =>
    let e1' := replace_var_with_value e1 index value in
    let e2' := replace_var_with_value e2 index value in
    App_stm B e1' e2'
  end.

Fixpoint replace_var_for_let (x : Rml) : Rml :=
  match x with
  | Let_stm n a b =>
    let b' := replace_var_for_let b in
    let a' := replace_var_for_let a in
    replace_var_with_value b' n a'
  | If_stm b m1 m2 =>
    let b' := replace_var_for_let b in
    let m1' := replace_var_for_let m1 in
    let m2' := replace_var_for_let m2 in
      If_stm b' m1' m2'
  | App_stm B e1 e2 =>
    let e1' := replace_var_for_let e1 in
    let e2' := replace_var_for_let e2 in
      App_stm B e1' e2'
  | _ => x
  end.

Definition example : Rml :=
  (If_stm (Const bool true)
          (Let_stm
             16 (Const bool true)
             (Let_stm
                12 (Const nat 4)
                (If_stm (Var 16) (Var 12) (Const nat 10))))
          (Const nat 900)).
   
Compute replace_var_for_let example.

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Inductive rml_trans_correct {A} : Rml -> @sRml A -> Prop :=
| const : forall (c : A), rml_trans_correct (Const A c) (sConst c)
| ifstm : 
    forall rmlb (srmlb : @sRml bool), @rml_trans_correct bool rmlb srmlb ->
    forall rmlm1 (srmlm1 : @sRml A), rml_trans_correct rmlm1 srmlm1 ->
    forall rmlm2 (srmlm2 : @sRml A), rml_trans_correct rmlm2 srmlm2 ->
       rml_trans_correct (If_stm rmlb rmlm1 rmlm2) (sIf_stm srmlb srmlm1 srmlm2)
| appstm :
    forall (B : Type),
    forall rmle1 (srmle1 : @sRml (B -> A)), @rml_trans_correct (B -> A) rmle1 srmle1 ->
    forall rmle2 (srmle2 : @sRml B), @rml_trans_correct B rmle2 srmle2 ->
      rml_trans_correct (App_stm B rmle1 rmle2) (sApp_stm B srmle1 srmle2).

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm B e1 e2).

Fixpoint is_rml_simple (x : Rml) : bool :=
  match x with
  | Var _ => false
  | Const _ _ => true
  | Let_stm n a b => false
  | If_stm b m1 m2 => is_rml_simple b && is_rml_simple m1 && is_rml_simple m2
  | App_stm B e1 e2 => is_rml_simple e1 && is_rml_simple e2
  end.

Lemma double_andb_true : forall {b1 b2}, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  destruct b1.
  - destruct b2 ; easy.
  - easy.
Qed.

Lemma triple_andb_true : forall {b1 b2 b3}, b1 && b2 && b3 = true <-> b1 = true /\ b2 = true /\ b3 = true.
Proof.
  destruct b1.
  - destruct b2.
    + destruct b3 ; easy.
    + easy.
  - easy.
Qed.
  
Theorem is_rml_simple_reflect_rml_is_simple :
  forall (x : Rml),
    is_rml_simple x = true <-> rml_is_simple x.
Proof.
  induction x.
  - simpl.
    easy.
  - simpl.
    split.
    + intros.
      apply is_const.
    + easy.
  - simpl.
    easy.
  - simpl.
    split.
    + intros.
      apply triple_andb_true in H.
      inversion H as [H1 [H2 H3]] ; clear H.
      apply is_if ; intuition.
    + intros.
      inversion H ; subst.
      intuition.
  - simpl.
    split.
    + intros.
      apply double_andb_true in H.
      inversion H ; clear H.
      apply is_app ; intuition.
    + intros.
      inversion H ; subst.
      intuition.
Qed.  

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type : Type -> Rml -> Prop :=
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B}, rml_valid_type A (Const B c)
| valid_if : forall (A : Type) b m1 m2, rml_valid_type bool b -> rml_valid_type A m1 -> rml_valid_type A m2 -> rml_valid_type A (If_stm b m1 m2)
| valid_app : forall (A B : Type) e1 e2, rml_valid_type (B -> A) e1 -> rml_valid_type B e2 -> rml_valid_type A (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml {A : Type} (rml : Rml) `{rml_simple : rml_is_simple rml} `{rml_valid : rml_valid_type A rml} : @sRml A.
Proof.
  (* apply is_rml_simple_reflect_rml_is_simple in rml_simple. *)
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (forall (A B : Type) c, rml_valid_type A (Const B c) -> A = B) by (intros ; inversion H ; subst ; reflexivity).
    assert (A = A0) by (apply (H A A0 a) ; assumption).
    subst.
    refine (sConst a).
  - exfalso.
    easy.
  - assert (if_valid_type : (rml_valid_type bool r1 /\ rml_valid_type A r2 /\ rml_valid_type A r3)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.
    
    refine (sIf_stm (@rml_to_sRml bool r1 s1 p1) (@rml_to_sRml A r2 s2 p2) (@rml_to_sRml A r3 s3 p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) r1 /\ rml_valid_type T r2) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : rml_is_simple r1 /\ rml_is_simple r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    apply (sApp_stm T (@rml_to_sRml (T -> A) r1 H1 p1) (@rml_to_sRml T r2 H2 p2)).
Defined.

Example correct_translation_const :
  forall A c, @rml_to_sRml A (@Const A c) (@is_const A c) (@valid_const A A c (erefl A)) = sConst c.
Proof. reflexivity. Qed.

Example correct_translation_if :
  forall A b n1 n2,
    let cb := (Const bool b) in
    let cn := (Const A n1) in
    let cns := (Const A n2) in
    @rml_to_sRml A
      (@If_stm cb cn cns)
      (@is_if cb cn cns (@is_const bool b) (@is_const A n1) (@is_const A n2))
      (@valid_if A cb cn cns (@valid_const bool bool b (@erefl Type bool)) (@valid_const A A n1 (erefl A)) (@valid_const A A n2 (erefl A)))
    = sIf_stm (sConst b) (sConst n1) (sConst n2).
Proof.  reflexivity. Qed.

Example correct_translation_app :
  forall (A B : Type) f x,
    let cf := (Const (A -> B) f) in
    let cx := (Const A x) in
    @rml_to_sRml B
      (@App_stm A cf cx)
      (@is_app A cf cx (@is_const (A -> B) f) (@is_const A x))
      (@valid_app B A cf cx (@valid_const (A -> B) (A -> B) f (erefl (A -> B))) (@valid_const A A x (erefl A)))
    = sApp_stm A (sConst f) (sConst x).
Proof. reflexivity. Qed.
  
(* -------------------------------------------------------------------------------- *)

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Definition valid_const' {A} c := @valid_const A A c (erefl A).
Definition is_const' {A} c := @is_const A c.

Definition rml_to_sRml_const {A} c := @rml_to_sRml A (Const A c) (is_const' c) (valid_const' c).

Compute interp_srml (rml_to_sRml_const 4).

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_for_let_simple :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x},
    rml_is_simple (replace_var_for_let x).
Proof.
  unfold replace_var_for_let.
  intros x.  
  induction x ; intros.
  - easy.
  - apply is_const.
  - easy.
  - inversion x_valid ; subst.
    inversion x_well.
    inversion H ; subst.
    apply is_if.
    + apply (IHx1 bool).
      * assumption.
      * apply well.
        assumption.
    + apply (IHx2 A).
      * assumption.
      * apply well.
        assumption.
    + apply (IHx3 A).
      * assumption.
      * apply well.
        assumption.
  - inversion x_valid ; subst.
    inversion x_well.
    inversion H ; subst.
    apply is_app.
    + apply (IHx1 (T -> A)).
      * assumption.
      * apply well.
        assumption.
    + apply (IHx2 T).
      * assumption.
      * apply well.
        assumption.
Qed.

Theorem replace_var_for_let_valid :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x},
    rml_valid_type A (replace_var_for_let x).
Proof.
  intros x A x_valid x_well.
  induction x_valid.
  - simpl.
    apply valid_const.
    assumption.
  - simpl.
    inversion x_well ; subst.
    inversion H ; subst.
    apply valid_if.
    + apply IHx_valid1.
      apply well.
      assumption.
    + apply IHx_valid2.
      apply well.
      assumption.
    + apply IHx_valid3.
      apply well.
      assumption.
  - simpl.
    inversion x_well ; subst.
    inversion H ; subst.
    apply valid_app.
    + apply IHx_valid1.
      apply well.
      assumption.
    + apply IHx_valid2.
      apply well.
      assumption.
Qed.

Definition computable_replace_var_for_let_valid x {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x} : rml_valid_type A (replace_var_for_let x).
Proof.
  (* apply (@replace_var_for_let_valid x A x_valid x_well). Defined. *)
  induction x_valid.
  - simpl.
    apply valid_const.
    assumption.
  - simpl.
    inversion x_well ; subst.
    inversion H ; subst.
    apply valid_if.
    + apply IHx_valid1.
      apply well.
      assumption.
    + apply IHx_valid2.
      apply well.
      assumption.
    + apply IHx_valid3.
      apply well.
      assumption.
  - simpl.
    inversion x_well ; subst.
    inversion H ; subst.
    apply valid_app.
    + apply IHx_valid1.
      apply well.
      assumption.
    + apply IHx_valid2.
      apply well.
      assumption.
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x} : continuation_monad_type R A :=
  let y := replace_var_for_let x in
  let y_simple := @replace_var_for_let_simple x A x_valid x_well in
  let y_valid := @computable_replace_var_for_let_valid x A x_valid x_well in
  (interp_srml (@rml_to_sRml A y y_simple y_valid)).

Compute @interp_rml _ (@Const nat 4) nat (@valid_const nat nat 4 (@erefl Type nat)) (@well (@Const nat 4) (@well_const nat 4 (@nil nat))).

(* -------------------------------------------------------------------------------- *)

Compute @interp_rml _ (@Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat)) _.
