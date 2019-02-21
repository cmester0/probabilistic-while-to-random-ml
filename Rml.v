Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From mathcomp Require Import ssreflect.choice.
From mathcomp Require Import analysis.posnum.
Require Import FunctionalExtensionality.

Definition flip {R : realType} x := @dflip R x. (* dflip *)
Definition range k : seq nat := (mkseq (fun x => x) k).
Definition random {R : realType} {T} k := @duni R T k.
(* Check random (10%:R :: nil). *)

(* FROM THE PAPER *)
Definition prandom {R : realType} {T : choiceType} k := fun f => @duni R T (mkseq f k).
Definition pflip {R : realType} := fun f => (@dflip R ((f true) / 2 + (f false) / 2)).

Reserved Notation "ma >>= f" (at level 40, left associativity).
Class Monad (M : Type -> Type) := {
  unit : forall {A}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
    where "ma >>= f" := (bind ma f);
  monad_law_unit_l : forall {A B} (a : A) (k : A -> M B), unit a >>= k = k a;
  monad_law_unit_r : forall {A} (ma : M A), ma >>= unit = ma;
  monad_law_assoc : forall {A B C} (ma : M A) (k : A -> M B) (h : B -> M C),
      ma >>= (fun a => k a >>= h) = ma >>= k >>= h
}.

Definition continuation_monad_type := fun ZO A => (A -> ZO) -> ZO.
Instance continuation_monad ZO : Monad (continuation_monad_type ZO) :=
  {
    unit := fun {A} (x : A) (f : A -> ZO) => f x ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

Definition probability_monad_type (R : realType) := continuation_monad_type R.
Instance probability_monad (R : realType) : Monad (probability_monad_type R) := continuation_monad R.

Inductive Rml {A} :=
| Var : nat -> Rml          
| Const : A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
| Fun_stm : nat -> A -> Rml -> Rml
| If_stm : (@Rml bool) -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.

Definition prob_unit {R} {A} (x : A) := @unit (probability_monad_type R) (probability_monad R) A x.
Definition prob_bind {R} {A B} mu M:= @bind (probability_monad_type R) (probability_monad R) A B mu M.

Definition Mif {R : realType} {A} (mu_b : (bool -> R) -> R) (mu1 : (A -> R) -> R) (mu2 : (A -> R) -> R) : (A -> R) -> R :=
  @prob_bind R bool A mu_b (fun b => if b then mu1 else mu2).

Fixpoint lookup {A} (default : A) (l : seq (nat * A)) (s : nat) : A :=
  match l with
  | (s',v) :: r =>
    if s == s'
    then v
    else lookup default r s
  | _ => default
  end.

Fixpoint interp {R : realType} {A} (default : A) (x : @Rml A) (l : seq (nat * A)) : probability_monad_type R A :=
  match x with
  | Var s => prob_unit (lookup default l s)
  | Const v => prob_unit v
  | Fun_stm x sigma t => (* TODO: unit *) interp default t ((x,sigma) :: l)
  | Let_stm x a b => prob_bind (interp default a l) (fun v => interp default b ((x, v) :: l))
  | If_stm b a1 a2 => Mif (interp false b nil) (interp default a1 l) (interp default a2 l)
  | App_stm e1 e2 => bind (interp default e1 l) (fun v => interp default e1 ((0%nat,v) :: l)) (* TODO: ORDERING? *)
                         (* TODO: replace 0 with correct index *)
  end.

Compute interp 0%nat (Var 0%nat) ((1%nat,10%nat) :: (0%nat,14%nat) :: nil).
