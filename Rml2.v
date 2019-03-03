Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.
Require Import FunctionalExtensionality.

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

(* -------------------------------------------------------------------------------- *)

Definition continuation_monad_type := fun ZO A => (A -> ZO) -> ZO.
Instance continuation_monad ZO : Monad (continuation_monad_type ZO) :=
  {
    unit := fun {A} (x : A) (f : A -> ZO) => f x ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

Definition cunit ZO {A} (x : A) : continuation_monad_type ZO A := fun (f : A -> ZO) => f x.
Definition cbind ZO {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) : continuation_monad_type ZO B := fun (f : B -> ZO) => mu (fun (x : A) => M x f).

Definition expectation_monad_type (R : realType) := continuation_monad_type R.
Instance expectation_monad (R : realType) : Monad (expectation_monad_type R) := continuation_monad R.

Definition obind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some y => f y
  | None => None
  end.

Instance option_monad : Monad option :=
  {
    unit := @Some;
    bind := @obind
  }.
Proof.
  all: try destruct x.
  all: reflexivity.
Qed.

Check @None.

(* -------------------------------------------------------------------------------- *)

(* Inductive Rml {A} : Type := *)
(* | Var : nat -> @Rml A *)
(* | Const : A -> @Rml A *)
(* | Let_stm : forall B, nat -> @Rml B -> @Rml A -> @Rml A *)
(* (* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A *) *)
(* | If_stm : @Rml bool -> @Rml A -> @Rml A -> @Rml A *)
(* | App_stm : forall B, @Rml (B -> A) -> @Rml B -> @Rml A. *)

Inductive Rml : Type :=
| Var : nat -> Rml
| Const : forall (A : Set), A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
(* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Set -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Fixpoint replace_var_with_value (x : Rml) (index : nat) (value : Rml) : option Rml :=
  match x with
  | Var n =>
    if n == index
    then Some value
    else Some x
  | Const A c => Some x
  | Let_stm n a b =>
    obind (replace_var_with_value a index value)
         (fun new_value =>
            if n == index
            then replace_var_with_value b index new_value
            else replace_var_with_value b index value)
  | If_stm b m1 m2 =>
    obind (replace_var_with_value b index value) (fun b' =>
    obind (replace_var_with_value m1 index value) (fun m1' =>
    obind (replace_var_with_value m2 index value) (fun m2' =>
      Some (If_stm b' m1' m2'))))
  | App_stm B e1 e2 =>
    obind (replace_var_with_value e1 index value) (fun e1' =>
    obind (replace_var_with_value e2 index value) (fun e2' =>
      Some (App_stm B e1' e2')))                     
  end.

Fixpoint replace_var_for_let (x : Rml) :=
  match x with
  | Let_stm n a b =>
    obind (replace_var_for_let b) (fun b' =>
    obind (replace_var_for_let a) (fun a' =>
    replace_var_with_value b' n a'))
  | If_stm b m1 m2 =>
    obind (replace_var_for_let b) (fun b' =>
    obind (replace_var_for_let m1) (fun m1' =>
    obind (replace_var_for_let m2) (fun m2' =>
      Some (If_stm b' m1' m2'))))
  | App_stm B e1 e2 =>
    obind (replace_var_for_let e1) (fun e1' =>
    obind (replace_var_for_let e2) (fun e2' =>
      Some (App_stm B e1' e2')))
  | _ => Some x
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

Inductive sRml {A : Set} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Set), @sRml (B -> A) -> @sRml B -> sRml.
(* | Fun_stm : forall B, nat -> B -> @sRml A -> @sRml A *)

Inductive rml_trans_correct {A} : Rml -> @sRml A -> Prop :=
| const : forall (c : A), rml_trans_correct (Const A c) (sConst c)
| ifstm : 
    forall rmlb (srmlb : @sRml bool), @rml_trans_correct bool rmlb srmlb ->
    forall rmlm1 (srmlm1 : @sRml A), rml_trans_correct rmlm1 srmlm1 ->
    forall rmlm2 (srmlm2 : @sRml A), rml_trans_correct rmlm2 srmlm2 ->
       rml_trans_correct (If_stm rmlb rmlm1 rmlm2) (sIf_stm srmlb srmlm1 srmlm2)
| appstm :
    forall (B : Set),
    forall rmle1 (srmle1 : @sRml (B -> A)), @rml_trans_correct (B -> A) rmle1 srmle1 ->
    forall rmle2 (srmle2 : @sRml B), @rml_trans_correct B rmle2 srmle2 ->
      rml_trans_correct (App_stm B rmle1 rmle2) (sApp_stm B srmle1 srmle2).

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Set) c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall (B : Set) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm B e1 e2).

Inductive rml_valid_type : Set -> Rml -> Prop :=
| valid_const : forall (A B : Set) (c : B) {_ : @eq Set A B}, rml_valid_type A (Const B c)
| valid_if : forall (A : Set) b m1 m2, rml_valid_type bool b -> rml_valid_type A m1 -> rml_valid_type A m2 -> rml_valid_type A (If_stm b m1 m2)
| valid_app : forall (A B : Set) e1 e2, rml_valid_type (B -> A) e1 -> rml_valid_type B e2 -> rml_valid_type A (App_stm B e1 e2).

Fixpoint rml_to_sRml {A : Set} (rml : Rml) `{_ : rml_is_simple rml} `{_ : rml_valid_type A rml}
  : @sRml A.
Proof.  
  case rml eqn : o_rml ; try (exfalso ; easy).
  - assert (forall (A B : Set) c, rml_valid_type A (Const B c) -> A = B) by (intros; inversion H ; subst ; easy).
    assert (A = A0) by (apply (H A A0 a) ; assumption).
    pose (a).
    rewrite <- H0 in a0.
    refine (sConst a0).
  - assert (if_valid_type : forall A r1 r2 r3, rml_valid_type A (If_stm r1 r2 r3) -> (rml_valid_type bool r1 /\ rml_valid_type A r2 /\ rml_valid_type A r3)) by (intros; inversion H; easy).
    pose (a := if_valid_type A r1 r2 r3 rml_valid_type0) ; inversion a as [p1 [p2 p3]] ; clear a.

    assert (if_is_simple : forall r1 r2 r3, rml_is_simple (If_stm r1 r2 r3) -> (rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3)) by (intros; inversion H ; easy).
    pose (if_is_simple r1 r2 r3 rml_is_simple0) ; inversion a as [s1 [s2 s3]] ; clear a.
    
    pose (b := @rml_to_sRml bool r1 s1 p1).
    pose (m1 := @rml_to_sRml A r2 s2 p2).
    pose (m2 := @rml_to_sRml A r3 s3 p3).
    
    refine (sIf_stm b m1 m2).
  - assert (app_valid_type : forall A B r1 r2, (rml_valid_type A (App_stm B r1 r2)) -> rml_valid_type (B -> A) r1 /\ rml_valid_type B r2) by (intros ; inversion H ; easy).
    
    pose (temp := app_valid_type A P r1 r2 rml_valid_type0).

    assert (app_is_simple : forall B r1 r2, rml_is_simple (App_stm B r1 r2) -> (rml_is_simple r1 /\ rml_is_simple r2)) by (intros; inversion H ; easy).
    pose (a := app_is_simple P r1 r2 rml_is_simple0) ; inversion a as [s1 s2] ; clear a.

    inversion temp as [p1 p2].
    pose (e1 := @rml_to_sRml (P -> A) r1 s1 p1).
    pose (e2 := @rml_to_sRml P r2 s2 p2).
    apply (sApp_stm P e1 e2).
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
      (@valid_if A cb cn cns (@valid_const bool bool b (erefl bool)) (@valid_const A A n1 (erefl A)) (@valid_const A A n2 (erefl A)))
    = sIf_stm (sConst b) (sConst n1) (sConst n2).
Proof. reflexivity. Qed.

Example correct_translation_app :
  forall (A B : Set) f x,
    let cf := (Const (A -> B) f) in
    let cx := (Const A x) in
    @rml_to_sRml B
      (@App_stm A cf cx)
      (@is_app A cf cx (@is_const (A -> B) f) (@is_const A x))
      (@valid_app B A cf cx (@valid_const (A -> B) (A -> B) f (erefl (A -> B))) (@valid_const A A x (erefl A)))
    = sApp_stm A (sConst f) (sConst x).
Proof. reflexivity. Qed.

Lemma simple_const_only_is_const :
  forall A c {k : rml_is_simple (Const A c)}, k = is_const A c.
Proof.
Admitted.

Lemma valid_const_only_valid_const :
  forall A c {k : rml_valid_type A (Const A c)}, k = @valid_const A A c (erefl A).
Proof.
  intros.
  inversion k ; subst.
Admitted.

Theorem rml_to_sRml_correct :
  forall A rml `{simple : rml_is_simple rml} `{valid : rml_valid_type A rml},
    @rml_trans_correct A rml (@rml_to_sRml A rml simple valid).
Proof.
  intros.
  induction rml ; try (exfalso ; easy).
  - assert (A0 = A) by (inversion valid ; subst ; reflexivity) ; subst.
    assert (@sConst A a = @rml_to_sRml A (Const A a) simple valid).
    + rewrite (@simple_const_only_is_const A a simple).
      rewrite (@valid_const_only_valid_const A a valid).
      apply (correct_translation_const A a).      
    + rewrite <- H. apply const.
  - inversion simple ; subst.
    inversion valid ; subst.

    pose (p1 := (@rml_to_sRml bool rml1 H2 H6)).
    pose (p2 := (@rml_to_sRml A rml2 H3 H7)).
    pose (p3 := (@rml_to_sRml A rml3 H4 H8)).    
    
    assert (@sIf_stm A p1 p2 p3 = @rml_to_sRml A (If_stm rml1 rml2 rml3) simple valid).
    +
Admitted.

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => cunit R c
  | sIf_stm b m1 m2 => bind (interp_srml b) (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => bind (interp_srml e1) (fun (g : C -> A) => bind (interp_srml e2) (fun k => unit (g k)))
  end.

Definition valid_const' {A} c := @valid_const A A c (erefl A).
Definition is_const' {A} c := @is_const A c.

Definition rml_to_sRml_const {A} c := @rml_to_sRml A (Const A c) (is_const' c) (valid_const' c).

Compute interp_srml (rml_to_sRml_const 4).

(* Inductive var_in_rml_scope : nat -> Rml -> Prop := *)
(* | var_in_var : forall n, var_in_rml_scope n (Var n) *)
(* | var_in_let1 : forall n1 n2 rml1 rml2, var_in_rml_scope n1 rml1 -> var_in_rml_scope n1 (Let_stm n2 rml1 rml2) *)
(* | var_in_let2 : forall n1 n2 rml1 rml2, n1 <> n2 -> var_in_rml_scope n1 rml2 -> var_in_rml_scope n1 (Let_stm n2 rml1 rml2). *)

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

Theorem y_is_simple :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x},
  forall y, (replace_var_for_let x) = Some y -> rml_is_simple y.
Proof.
  intros x.
  induction x ; intros.
  - easy.
  - destruct y ; try easy.
    + apply is_const.
  - destruct y ; try easy.
  - simpl in H.
    unfold obind in H.
    (do 3 destruct replace_var_for_let) ; inversion H.
    inversion x_valid ; subst.
    inversion x_well ; subst.
    inversion H0 ; subst.
    apply is_if.
    + apply (IHx1 bool).
      * assumption.
      * apply well.
         assumption.
      * reflexivity.
    + apply (IHx2 A).
      * assumption.
      * apply well.
         assumption.
      * reflexivity.
    + apply (IHx3 A).
      * assumption.
      * apply well.
         assumption.
      * reflexivity.
  - simpl in H.
    (do 2 destruct replace_var_for_let) ; inversion H.
    inversion x_valid ; subst.
    inversion x_well ; subst.
    inversion H0 ; subst.
    apply is_app.
    + apply (IHx1 (P -> A)).
      * assumption.
      * apply well.
        assumption.
      * reflexivity.
    + apply (IHx2 P).
      * assumption.
      * apply well.
        assumption.
      * reflexivity.
Qed.

Theorem y_is_valid :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x},
  forall y, (replace_var_for_let x) = Some y -> rml_valid_type A y.
Proof.
Admitted.

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x} `{x_well : well_formed_empty x} : option (continuation_monad_type R A).
  case (replace_var_for_let x) eqn : first_pass_old.
  - refine (Some (interp_srml (@rml_to_sRml A r (@y_is_simple x A x_valid x_well r first_pass_old) (@y_is_valid x A x_valid x_well r first_pass_old)))).
  - refine None.
Defined.