From mathcomp Require Import boolp.

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
    unit := fun {A} (x : A) => (fun f => f x) ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

Instance option_monad : Monad (@option) :=
  {
    unit := fun {A} (x : A) => Some x ;
    bind := fun {A B} (x : option A) (f : A -> option B) =>
              match x with
              | Some y => f y
              | None => None
              end
  }. 
Proof.
  reflexivity.
  destruct x ; reflexivity.
  destruct x.
  intros.
  destruct (k a).
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

(* -------------------------------------------------------------------------------- *)

Lemma pselect_left :
  forall (P : Prop),
    P -> exists x, pselect P = left x.
Proof.
  intros.
  destruct pselect.
  - exists p.
    reflexivity.
  - contradiction.
Qed.

Lemma pselect_left_eq :
  forall {A} P,
    exists x, pselect (@eq A P P) = left x.
Proof.
  intros.
  destruct pselect.
  - exists e.
    reflexivity.
  - contradiction.
Qed.
