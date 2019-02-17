Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From mathcomp Require Import ssreflect.choice.
From mathcomp Require Import analysis.posnum.

Check 2.

Definition flip {R : realType} x := @dflip R x. (* dflip *)
(* Check random 10%:R. *)

Definition range k : seq nat := (mkseq (fun x => x) k).

Definition random {R : realType} {T} k := @duni R T k.

(* FROM THE PAPER *)
Definition prandom {R : realType} {T : choiceType} k := fun f => @duni R T (mkseq f k).
Definition pflip {R : realType} := fun f => (@dflip R ((f true) / 2 + (f false) / 2)).

Definition unit {R} :=
  fun {A : choiceType} (x : A) =>
    @dunit R A x.

Definition bind {R} :=
  fun {A B : choiceType} (x : distr R A) (f : A -> distr R B) =>
    dlet f x.

Theorem bind_unit :
  forall R A B,
  forall x M,
    @bind R A B (unit x) M =1 M x.
Proof.
  intros.
  apply dlet_unit.
Qed.

Theorem bind_bind :
  forall R A B,
  forall mu M1 M2,
    @bind R A B (bind mu M1) M2 =1 @bind R A B mu (fun x => bind (M1 x) M2).
Proof.
  intros.
  apply dlet_dlet.
Qed.

Theorem bind_unit_id :
  forall R A,
  forall mu,
    @bind R A A mu (@unit R A) =1 mu.
Proof.
  intros.
  apply dlet_dunit_id.
Qed.

Inductive Rml {R} {A : choiceType} :=
| Var : A -> Rml          
| Const : A -> Rml
| Let_stm : Rml -> Rml -> Rml
| Fun_stm : (A -> distr R A) -> Rml -> Rml
| If_stm : (@Rml R bool_choiceType) -> Rml -> Rml -> Rml.

Fixpoint interp {R : realType} {A : choiceType} (x : @Rml R A) : distr R A :=
  match x with
  | Var v => @unit R A v
  | Const v => @unit R A v
  | Let_stm a b => @bind R A A (interp a) (fun x => interp b)
  | Fun_stm f x => bind (interp x) f
  | If_stm b a1 a2 =>
    @bind R _ A (@interp R bool_choiceType b) (fun (x : bool) =>
                                                 if x
                                                 then interp a1
                                                 else interp a2)
  end.

