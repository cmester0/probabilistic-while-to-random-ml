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
| Const : forall A, A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
(* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.

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
  | App_stm e1 e2 =>
    obind (replace_var_with_value e1 index value) (fun e1' =>
    obind (replace_var_with_value e2 index value) (fun e2' =>
      Some (App_stm e1' e2')))                     
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
  | App_stm e1 e2 =>
    obind (replace_var_for_let e1) (fun e1' =>
    obind (replace_var_for_let e2) (fun e2' =>
      Some (App_stm e1' e2')))
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

Inductive sRml {A} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall B, @sRml (B -> A) -> @sRml B -> sRml.
(* | Fun_stm : forall B, nat -> B -> @sRml A -> @sRml A *)

Inductive rml_trans_correct {A} : Rml -> @sRml A -> Prop :=
| const : forall (c : A), rml_trans_correct (Const A c) (sConst c)
| ifstm : 
    forall rmlb (srmlb : @sRml bool), @rml_trans_correct bool rmlb srmlb ->
    forall rmlm1 (srmlm1 : @sRml A), rml_trans_correct rmlm1 srmlm1 ->
    forall rmlm2 (srmlm2 : @sRml A), rml_trans_correct rmlm2 srmlm2 ->
       rml_trans_correct (If_stm rmlb rmlm1 rmlm2) (sIf_stm srmlb srmlm1 srmlm2)
| appstm :
    forall B,
    forall rmle1 (srmle1 : @sRml (B -> A)), @rml_trans_correct (B -> A) rmle1 srmle1 ->
    forall rmle2 (srmle2 : @sRml B), @rml_trans_correct B rmle2 srmle2 ->
      rml_trans_correct (App_stm rmle1 rmle2) (sApp_stm B srmle1 srmle2).

Fixpoint sRml_to_rml {A} (srml : @sRml A) :=
  match srml with
  | sConst c => Const A c
  | sIf_stm b m1 m2 => If_stm (sRml_to_rml b) (sRml_to_rml m1) (sRml_to_rml m2)
  | sApp_stm B f x => App_stm (sRml_to_rml f) (sRml_to_rml x)
  end.

Theorem transform_correctness_inverse :
  forall A srml, rml_trans_correct (@sRml_to_rml A srml) srml.
Proof.
  intros.
  induction srml.
  - simpl.
    apply const.
  - simpl.
    apply (@ifstm A (sRml_to_rml srml1) srml1 IHsrml1 (sRml_to_rml srml2) srml2 IHsrml2 (sRml_to_rml srml3) srml3 IHsrml3).
  - simpl.
    apply (@appstm A B (sRml_to_rml srml1) srml1 IHsrml1 (sRml_to_rml srml2) srml2 IHsrml2).
Qed.

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall A c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm e1 e2).

Inductive rml_valid_type : Type -> Rml -> Prop :=
| valid_const : forall A B (c : B) {_ : A = B}, rml_valid_type A (Const B c)
| valid_if : forall A b m1 m2, rml_valid_type bool b -> rml_valid_type A m1 -> rml_valid_type A m2 -> rml_valid_type A (If_stm b m1 m2)
| valid_app : forall A B e1 e2, rml_valid_type (B -> A) e1 -> rml_valid_type B e2 -> rml_valid_type A (App_stm e1 e2).

Fixpoint rml_to_sRml {A} (rml : Rml) `{_ : rml_is_simple rml} `{_ : rml_valid_type A rml}
  : @sRml A.
Proof.  
  case rml eqn : o_rml ; try (exfalso ; easy).
  - assert (forall A B c, rml_valid_type A (Const B c) -> A = B) by (intros; inversion H ; easy).
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
  - assert (app_valid_type : forall A r1 r2, rml_valid_type A (App_stm r1 r2) -> exists B, (rml_valid_type (B -> A) r1 /\ rml_valid_type B r2)) by (intros ; inversion H ; exists B ; easy).
    
    pose (temp := app_valid_type A r1 r2 rml_valid_type0). 

    assert (app_is_simple : forall r1 r2, rml_is_simple (App_stm r1 r2) -> (rml_is_simple r1 /\ rml_is_simple r2)) by (intros; inversion H ; easy).
    pose (a := app_is_simple r1 r2 rml_is_simple0) ; inversion a as [s1 s2] ; clear a.
    
    assert (exists (B : Type), True).
    + inversion temp as [x [p1 p2]].
      pose (e1 := @rml_to_sRml (x -> A) r1 s1 p1).
      pose (e2 := @rml_to_sRml x r2 s2 p2).
      pose (solution := sApp_stm x e1 e2).
      exists x.
      easy.
Admitted.

Fixpoint interp {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => cunit R c
  | sIf_stm b m1 m2 => bind (interp b) (fun (t : bool) => if t then (interp m1) else (interp m2))
  | sApp_stm C e1 e2 => bind (interp e1) (fun (g : C -> A) => bind (interp e2) (fun k => unit (g k)))
  end.

Fixpoint interp_rml {R} (x : Rml) {A} (rml : Rml) `{_ : rml_valid_type A rml} : option (continuation_monad_type R A) :=
  obind (replace_var_for_let x) (fun y => Some (interp (rml_to_sRml y))).