Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From mathcomp Require Import ssreflect.choice.
From mathcomp Require Import analysis.posnum.
Require Import FunctionalExtensionality.

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

Inductive Rml {R : realType} {A : choiceType} :=
| Var : nat_choiceType -> Rml          
| Const : A -> @Rml R A
| Let_stm : nat_choiceType -> Rml -> Rml -> Rml
| Fun_stm : nat_choiceType -> choiceType -> Rml -> Rml
| If_stm : (@Rml R bool_choiceType) -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.

Definition Mif {R B} (mu_b : distr R bool_choiceType) mu1 mu2 :=
  @bind R bool_choiceType B mu_b (fun b => if b then mu1 else mu2).

Fixpoint interp {R : realType} {A : choiceType} (x : @Rml R A) (l : seq (nat_choiceType * A)) :
  distr R A :=
  match x with
  | Var s =>
    (fix let_rec l := match l with | nil => dnull | (s',v) :: r => if s == s' then @unit R A v else let_rec r end) l
  | Const v => @unit R A v
  | Let_stm x a b => @bind R A A (interp a l) (fun v => interp b ((x, v) :: l))
  | Fun_stm x sigma t => bind dnull (fun v => interp t ((x,v) :: l))
  | If_stm b a1 a2 => Mif (interp b nil) (interp a1 l) (interp a2 l)
  | App_stm e1 e2 => bind (interp e2 l) (fun v => interp e1 ((0%nat,v) :: l)) (* Todo: replace 0 with correct index *)
  end.

