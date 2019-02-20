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

Reserved Notation "ma >>= f" (at level 40, left associativity).
Class Monad (M : choiceType -> Type) : Prop := {
  unit : forall {A : choiceType}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
    where "ma >>= f" := (bind ma f);
  monad_law_unit_l : forall {A B : choiceType} (a : A) (k : A -> M B), unit a >>= k = k a;
  monad_law_unit_r : forall {A} (ma : M A), ma >>= unit = ma;
  monad_law_assoc : forall {A B C} (ma : M A) (k : A -> M B) (h : B -> M C),
      ma >>= (fun a => k a >>= h) = ma >>= k >>= h
}.

Instance monad_monad : Monad (fun x => x) :=
  {
    unit := fun A => (fun x => x) ;
    bind := fun A B => (fun x => (fun f => f x))
  }.
Proof.
  all: reflexivity.
Qed.

Instance continuation_monad R : Monad (fun T => (T -> R) -> R) :=
  {
    unit := fun {A} (x : A) => (fun f => f x) ;
    bind := fun {A B} => fun x => fun f => (fun (g : B -> R) => x (fun a => f a g))
  }.
Proof. all: reflexivity. Qed.

Check (fun f => finfun_of_choiceType f).

Instance continuation_monad' (type_func : choiceType -> Type) : Monad (fun A => forall T, (A -> type_func T) -> (type_func T)) :=
  {
    unit := fun {A} (x : A) => (fun T => (fun f => f x) ) ;
    bind := fun {A B} (x : (fun A => forall T, (A -> type_func T) -> (type_func T)) A) => (fun (f : A -> forall T : choiceType, (B -> type_func T) -> type_func T) => (fun T => (fun (g : B -> type_func T) => x T (fun a => f a T g))))
  }.
Proof. all: reflexivity. Qed.

Definition continuation_monad_unit {R : realType} := fun {A} (x : A) => (fun (T : choiceType) => (fun (f : A -> distr R T) => f x)).
Definition continuation_monad_bind {R : realType} := fun {A} (x : A) => fun {A B} (x : (fun A => forall T, (A -> distr R T) -> (distr R T)) A) => (fun (f : A -> forall T : choiceType, (B -> distr R T) -> distr R T) => (fun T => (fun (g : B -> distr R T) => x T (fun a => f a T g)))).

Instance continuation_monad'' R : Monad (fun A => forall T, (A -> distr R T) -> (distr R T)) :=
  {
    unit := fun {A} (x : A) => (fun T => (fun f => f x) ) ;
    bind := fun {A B} (x : (fun A => forall T, (A -> distr R T) -> (distr R T)) A) => (fun (f : A -> forall T : choiceType, (B -> distr R T) -> distr R T) => (fun T => (fun (g : B -> distr R T) => x T (fun a => f a T g))))
  }.
Proof. all: reflexivity. Qed.

Axiom all_choice : choiceType = Type.

Instance continuation_monad''' R : Monad (fun A => (A -> distr R A) -> (distr R A)) :=
  {
    unit := fun {A} (x : A) => (fun f => f x) ;
    bind := fun {A B} (x : (fun A => (A -> distr R A) -> (distr R A))) => (fun (f : A -> forall T : choiceType, (B -> distr R T) -> distr R T) => (fun T => (fun (g : B -> distr R T) => x T (fun a => f a T g))))
  }.
Proof. all: reflexivity. Qed.

Inductive Rml {R : realType} {A : choiceType} :=
| Var : nat_choiceType -> Rml          
| Const : A -> @Rml R A
| Let_stm : nat_choiceType -> Rml -> Rml -> Rml
| Fun_stm : nat_choiceType -> choiceType -> Rml -> Rml
| If_stm : (@Rml R bool_choiceType) -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.

Check continuation_monad_bind.

Definition cm_bind {R} := fun {A B} (x : (fun A => forall T, (A -> distr R T) -> (distr R T)) A) => (fun (f : A -> forall T : choiceType, (B -> distr R T) -> distr R T) => (fun T => (fun (g : B -> distr R T) => x T (fun a => f a T g)))).

Definition Mif {R B} (mu_b : (bool_choiceType -> distr R bool_choiceType) -> distr R bool_choiceType) (mu1 : distr R B) (mu2 : distr R B) : distr R B.
Proof.
  pose bind := @cm_bind.
  Check bind R bool_choiceType B (fun T => mu_b).
  
Definition continuation_monad_bind {R : realType} := fun {A} (x : A) => fun {A B} (x : (fun A => forall T, (A -> distr R T) -> (distr R T)) A) => (fun (f : A -> forall T : choiceType, (B -> distr R T) -> distr R T) => (fun T => (fun (g : B -> distr R T) => x T (fun a => f a T g)))).


  :=
  @bind R bool_choiceType B mu_b (fun b => if b then mu1 else mu2).

(* Convert to continuations *)
Fixpoint interp {R : realType} {A : choiceType} (x : @Rml R A) (l : seq (nat_choiceType * A)) :
  (A -> distr R A) -> distr R A.
Proof.
  case x ; clear x.
  - intros s.
    refine 
       (fun x => (fix let_rec l :=
          match l with
          | nil => dnull
          | (s',v) :: r =>
            if s == s'
            then @unit R A v x
            else (fun x => let_rec r) x
          end) l).
  - intros v.
    refine (fun x => @unit R A v x).
  - intros x a b.
    refine (@bind R A A (@interp R A a l) (fun v => @interp R A b ((x, v) :: l))).
  - intros x sigma t.
    Check unit.
    Check unit (fun x => x).
    
    refine (fun g => @interp R A t l (fun v => g v)).
Defined.
    
Fixpoint interp {R : realType} {A : choiceType} (x : @Rml R A) (l : seq (nat_choiceType * A)) :
  (A -> distr R A) -> distr R A :=
  match x with
  | Var s =>
    (fun x =>
       (fix let_rec l :=
          match l with
          | nil => dnull
          | (s',v) :: r =>
            if s == s'
            then @unit R A v x
            else (fun x => let_rec r) x
          end) l)
  | Const v => (fun x => @unit R A v x)
  | Let_stm x a b => @bind R A A (interp a l) (fun v => interp b ((x, v) :: l))
  | Fun_stm x sigma t => (fun g => interp t l (fun v => g v))
  | If_stm b a1 a2 => Mif (interp b nil) (interp a1 l) (interp a2 l)
  | App_stm e1 e2 => bind (interp e2 l) (fun v => interp e1 ((0%nat,v) :: l)) (* Todo: replace 0 with correct index *)
  end.
