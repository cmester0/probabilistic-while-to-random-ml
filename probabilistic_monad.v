(* - Create monad of probabilistic monad. (FCF paper) *)
(*   + Axiom of choice. *)
(*   + Unit(x) = 1_x (unit distribution) *)
(*   + Bind(f,x) = Expectation (f(x)) *)
(* - Giry monad (finite, ...) .. {domain theory}. *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import ssreflect.choice.
From xhl Require Import prhl.prhl.
From mathcomp Require Import analysis.reals.
Require Import FunctionalExtensionality.
From Hammer Require Import Hammer Reconstr.

Check dlet.
Check dunit.
Check mlet.
Check \dlet_(i <- dnull) dnull.

Definition unit_giry {T} {A : choiceType} (x : A) : distr T A :=
  dunit x.

Definition bind_giry {T} {A B : choiceType} (x : distr T A) (f : A -> distr T B) : distr T B :=
  (esp (dlet f x)).

Class monad {M : choiceType -> Type} :=
  {
    unit : forall {A : choiceType}, A -> M A;
    bind : forall {A B : choiceType}, M A -> (A -> M B) -> M B;

    r0 : forall (A B : choiceType) (f : A -> M B) (x : A), @bind A B (@unit A x) f = f x;
    r1 : forall (A : choiceType) (m : M A), @bind A A m (@unit A) = m ;
    r2 : forall (A B C : choiceType) (f : A -> M B) (g : B -> M C) (m : M A),
        @bind B C (@bind A B m f) g = @bind A C m (fun x => @bind B C (f x) g)
  }.

Class monad_giry T : @monad (distr T) :=
  {
    unit : forall {A : choiceType}, A -> distr T A;
    bind : forall {A B}, distr T A -> (A -> distr T B) -> distr T B;

    r0 : forall (A B : choiceType) (f : A -> distr T B) (x : A), @bind A B (unit x) f =1 f x;
    r1 : forall A (m : distr T A), @bind A A m (@unit A) =1 m ;
    r2 : forall (A B C : choiceType) (f : A -> distr T B) (g : B -> distr T C) (m : distr T A),
        @bind B C (@bind A B m f) g =1 @bind A C m (fun x => @bind B C (f x) g)
  }.

Instance monad_giry_instance T : @monad_giry T :=
  {
    unit := @unit_giry T ;
    bind := @bind_giry T
  }.
Proof.
  - intros.
    simpl.
    unfold bind_giry.
    unfold unit_giry.
    apply dlet_unit.
  - intros.
    unfold bind_giry.
    unfold unit_giry.
    apply dlet_dunit_id.
  - intros.
    unfold bind_giry.
    apply dlet_dlet.
Qed.



Class monad_giry T :=
  {
    unit : forall {A : choiceType}, A -> distr T A;
    bind : forall {A B}, distr T A -> (A -> distr T B) -> distr T B;

    r0 : forall (A B : choiceType) (f : A -> distr T B) (x : A), @bind A B (unit x) f =1 f x;
    r1 : forall A (m : distr T A), @bind A A m (@unit A) =1 m ;
    r2 : forall (A B C : choiceType) (f : A -> distr T B) (g : B -> distr T C) (m : distr T A),
        @bind B C (@bind A B m f) g =1 @bind A C m (fun x => @bind B C (f x) g)
  }.

Definition unit_giry {T} {A : choiceType} (x : A) : distr T A :=
  dunit x.

Definition bind_giry {T} {A B} (x : distr T A) (f : A -> distr T B) : distr T B :=
  dlet f x.

Instance monad_giry_instance T : @monad_giry T :=
  {
    unit := @unit_giry T ;
    bind := @bind_giry T
  }.
Proof.
  - intros.
    simpl.
    unfold bind_giry.
    unfold unit_giry.
    apply dlet_unit.
  - intros.
    unfold bind_giry.
    unfold unit_giry.
    apply dlet_dunit_id.
  - intros.
    unfold bind_giry.
    apply dlet_dlet.
Qed.
