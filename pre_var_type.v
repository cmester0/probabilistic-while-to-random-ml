From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.reals.

(* -------------------------------------------------------------------------------- *)

Lemma nat_S_equal :
  forall n x, (n.+1 == x.+1) = true <-> (n == x) = true.
Proof.
  induction n ; destruct x ; try easy ; try reflexivity.
Qed.

Lemma nat_equal :
  forall (n x : nat), n = x <-> (n == x) = true.
Proof.
  induction n ; destruct x ; try easy ; try reflexivity.
  split.
  - intros.
    inversion H.
    inversion H.
    apply nat_S_equal.
    apply (IHn x) in H1.
    rewrite H2 in H1.
    assumption.
  - intros.
    pose (nat_S_equal n x).
    symmetry in i.
    apply i in H.
    apply (IHn x) in H.
    rewrite H.
    reflexivity.
Qed.

Lemma nat_refl_equal :
  forall x : nat, (x == x) = true.
Proof.
  intros.
  pose (nat_equal x x).
  rewrite <- i.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------------- *)

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
| well_var : forall x l, List.In x l -> well_formed l (Var x)
| well_const : forall A c l, well_formed l (Const A c)
| well_let_stm : forall x e1 e2 l, well_formed l e1 -> well_formed (x :: l) e2 -> well_formed l (Let_stm x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Compute (well_let_stm 10 (Const nat 4) (Var 10) nil (well_const nat 4 nil) (well_var 10 [:: (10)] _)).

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
    else Let_stm n new_value (replace_var_with_value b index value)
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

Inductive replaced_var_in_rml : nat -> Type -> Rml -> Rml -> Rml -> Prop :=
| replaced_var_diff : forall n0 n1 y, (n1 == n0) = false -> replaced_var_in_rml n0 y (Var n1) (Var n1)
| replaced_var_same : forall n y, replaced_var_in_rml n y (Var n) y
| replaced_const : forall n y, forall A c, replaced_var_in_rml n y (Const A c) (Const A c)
| replaced_let_diff : forall n0 n1 y, forall a b a' b', (n1 == n0) = false -> replaced_var_in_rml n0 y a a' -> replaced_var_in_rml n0 y b b' -> replaced_var_in_rml n0 y (Let_stm n1 a b) (Let_stm n1 a' b')
| replaced_let_same : forall n y, forall a b a' b', replaced_var_in_rml n y a a' -> replaced_var_in_rml n a' b b' -> replaced_var_in_rml n y (Let_stm n a b) b'
| replace_if : forall n y, forall b m1 m2 b' m1' m2', replaced_var_in_rml n y b b' -> replaced_var_in_rml n y m1 m1' -> replaced_var_in_rml n y m2 m2' -> replaced_var_in_rml n y (If_stm b m1 m2) (If_stm b' m1' m2')
| replace_app : forall n y, forall B e1 e2 e1' e2', replaced_var_in_rml n y e1 e1' -> replaced_var_in_rml n y e2 e2' -> replaced_var_in_rml n y (App_stm B e1 e2) (App_stm B e1' e2').

Theorem replace_var_with_value_correctness :
  forall x n y, replaced_var_in_rml n y x (replace_var_with_value x n y).
Proof.
  induction x ; intros.
  - simpl.
    destruct (n == n0) eqn : n0n.
    + apply nat_equal in n0n ; subst.
      apply replaced_var_same.
    + apply replaced_var_diff.
      assumption.
  - simpl.
    apply replaced_const.
  - simpl.
    destruct (n == n0) eqn : n0n.
    + apply nat_equal in n0n ; subst.
      apply (replaced_let_same n0 y x1 x2 (replace_var_with_value x1 n0 y)) ; easy.
    + apply replaced_let_diff ; easy.
  - apply replace_if ; easy.
  - apply replace_app ; easy.
Qed.

Theorem replace_var_with_value_refl :
  forall x n y k, replaced_var_in_rml n y x k <-> replace_var_with_value x n y = k.
Proof.
  split ; intros.
  - induction H ; simpl ; try rewrite H ; try rewrite (nat_refl_equal n) ; try rewrite (nat_refl_equal n) ; subst ; try reflexivity.
    + 
  - subst.
    apply replace_var_with_value_correctness.
Qed.
      
(* TODO: Make proof for correctness these two definitions *)

Fixpoint replace_var_for_let_aux (x : Rml) {l} `{x_well : well_formed l x}: Rml.
  case x eqn : x_old.
  - (* Var *)
    intros.
    induction l.
    + easy.
    + refine x.
    
  - (* Const *)
    intros. refine x.
  - (* Let *)
    assert (a_well : well_formed l r1) by (inversion x_well ; subst ; assumption).
    assert (b_well : well_formed (n :: l) r2) by (inversion x_well ; subst ; assumption).
    
    refine (let a' := replace_var_for_let_aux r1 l a_well in
            let b' := replace_var_for_let_aux r2 (n :: l) b_well in
            replace_var_with_value b' n a').
  - (* If *)
    assert (b_well : well_formed l r1) by (inversion x_well ; subst ; assumption).
    assert (m1_well : well_formed l r2) by (inversion x_well ; subst ; assumption).
    assert (m2_well : well_formed l r3) by (inversion x_well ; subst ; assumption).

    refine (let b' := replace_var_for_let_aux r1 l b_well in
            let m1' := replace_var_for_let_aux r2 l m1_well in
            let m2' := replace_var_for_let_aux r3 l m2_well in
            If_stm b' m1' m2').
  - (* App *)
    assert (e1_well : well_formed l r1) by (inversion x_well ; subst ; assumption).
    assert (e2_well : well_formed l r2) by (inversion x_well ; subst ; assumption).

    refine (let e1' := replace_var_for_let_aux r1 l e1_well in
            let e2' := replace_var_for_let_aux r2 l e2_well  in
            App_stm T e1' e2').
Defined.

Definition replace_var_for_let (x : Rml) `{x_well : well_formed nil x} : Rml :=
  @replace_var_for_let_aux x nil x_well.

Check List.fold_left.

Check List.remove.

Definition example : Rml :=
  (If_stm (Const bool true)
          (Let_stm
             16 (Const bool true)
             (Let_stm
                12 (Const nat 4)
                (If_stm (Var 16) (Var 12) (Const nat 10))))
          (Const nat 900)).

Compute replace_var_with_value example 16 (Const bool true).
Compute replace_var_with_value example 12 (Const nat 4).   
Compute replace_var_for_let example.

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type : Type -> Rml -> seq (nat * Type) -> Prop :=
| valid_var : forall x l A, List.In (x,A) l -> rml_valid_type A (Var x) l
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B} l, rml_valid_type A (Const B c) l
| valid_let : forall A B x a b l, rml_valid_type B a l -> rml_valid_type A b ((x,B) :: l) -> rml_valid_type A (Let_stm x a b) l
| valid_if : forall (A : Type) b m1 m2 l, rml_valid_type bool b l -> rml_valid_type A m1 l -> rml_valid_type A m2 l -> rml_valid_type A (If_stm b m1 m2) l
| valid_app : forall (A B : Type) e1 e2 l, rml_valid_type (B -> A) e1 l -> rml_valid_type B e2 l -> rml_valid_type A (App_stm B e1 e2) l.

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml {A : Type} (rml : Rml) `{rml_simple : rml_is_simple rml} `{rml_valid : rml_valid_type A rml nil} : @sRml A.
Proof.
  (* apply is_rml_simple_reflect_rml_is_simple in rml_simple. *)
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (forall (A B : Type) c l, rml_valid_type A (Const B c) l -> A = B) by (intros ; inversion H ; subst ; reflexivity).
    assert (A = A0) by (apply (H A A0 a nil) ; assumption).
    subst.
    refine (sConst a).
  - exfalso.
    easy.
  - assert (if_valid_type : (rml_valid_type bool r1 nil /\ rml_valid_type A r2 nil /\ rml_valid_type A r3 nil)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.
    
    refine (sIf_stm (@rml_to_sRml bool r1 s1 p1) (@rml_to_sRml A r2 s2 p2) (@rml_to_sRml A r3 s3 p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) r1 nil /\ rml_valid_type T r2 nil) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : rml_is_simple r1 /\ rml_is_simple r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    apply (sApp_stm T (@rml_to_sRml (T -> A) r1 H1 p1) (@rml_to_sRml T r2 H2 p2)).
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Lemma replace_let_helper_lemma_simple :
  forall v1 v2 n, rml_is_simple v1 -> rml_is_simple (replace_var_with_value v1 n v2).
Proof.
  induction v1 ; intros.
  - easy.
  - apply is_const.
  - easy.
  - simpl in *.    
    inversion_clear H as [H1 | H2 | H3] ; subst.
    
    apply is_if.
    + apply IHv1_1. assumption.
    + apply IHv1_2. assumption.
    + apply IHv1_3. assumption.
  - simpl in *.
    inversion_clear H as [H1 | H2 | H3] ; subst.

    apply is_app.
    + apply IHv1_1. assumption.
    + apply IHv1_2. assumption.
Qed.

Lemma not_or_is_not :
  forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  intros.
  intuition.
Qed.

Compute replace_var_with_value (Let_stm 4 (Const nat 4) (Var 4)).

Theorem replace_var_for_with_value_valid :
  forall (x y : Rml) n l {A} `{x_valid : rml_valid_type A x l} `{y_valid : rml_valid_type A y l}, forall z, replaced_var_in_rml n y x z -> rml_valid_type A z l.
Proof.
  induction x ; intros.
  - inversion H ; subst.
    + apply valid_var.
      inversion x_valid ; subst.
      assumption.
    + apply y_valid.
  - inversion H ; subst.
    inversion x_valid ; subst.
    apply valid_const.
    reflexivity.
  - inversion H ; subst.
    + inversion x_valid ; subst.
      apply valid_let with (B := B).
      * apply (IHx1 y n).
        apply H6.
        
      
      
Qed.

Theorem replace_var_for_let_valid :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x nil} `{x_well : well_formed nil x},
    rml_valid_type A (@replace_var_for_let x x_well) nil.
Proof.
  unfold replace_var_for_let.
  induction x ; intros.
  - inversion x_well ; subst.
    easy.
  - simpl.
    apply valid_const.
    inversion x_valid ; subst.
    reflexivity.
  - simpl.
    inversion x_well ; subst.
    
    pose (@replace_var_for_let_aux x1 nil H2).
    pose (@replace_var_for_let_aux x2 [:: n] H4).

    inversion x_valid ; subst.
    pose (IHx2 A).

    
    
    elim x_well.
    inversion x_well.
    apply well_formed_weakening in H4.
    subst.
    inversion x_valid ; subst.
    apply valid_weakening in H7.
    pose (IHx2 H7 H4).

    pose (replace_let_helper_lemma_valid2 A B (@replace_var_for_let_aux x1 nil H2) (@replace_var_for_let_aux x2 nil H4) n nil).

    Set Printing All.
    
    apply r0.
    apply replace_let_helper_lemma_valid2.
    
    inversion x_valid ; subst.
    (* apply valid_weakening with (n := n) (B := B) in H11. *)
    (* pose (IHx2 H11 H4). *)
Admitted.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x nil} `{x_well : well_formed nil x} : continuation_monad_type R A :=
  let y := replace_var_for_let x in
  let y_simple := @replace_var_for_let_simple x A x_valid x_well in
  let y_valid := @replace_var_for_let_valid A x x_valid x_well in
  (interp_srml (@rml_to_sRml A y y_simple y_valid)).

(* -------------------------------------------------------------------------------- *)

(** * Examples **)

Compute @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil) _.

Compute @interp_rml _ (Let_stm 12 (@Const nat 4) (Var 12)) nat (@valid_let nat nat 12 (@Const nat 4) (Var 12) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat _)) _.
