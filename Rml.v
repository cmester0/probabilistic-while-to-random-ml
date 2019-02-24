Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

Definition flip {R : realType} x := @dflip R x. (* dflip *)
Definition range k : seq nat := (mkseq (fun x => x) k).
Definition random {R : realType} {T} k := @duni R T k.
(* Check random (10%:R :: nil). *)

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

(* Inductive Rml {A} := *)
(* | Var : nat -> Rml           *)
(* | Const : A -> Rml *)
(* | Let_stm : nat -> Rml -> Rml -> Rml *)
(* | Fun_stm : nat -> A -> Rml -> Rml *)
(* | If_stm : (@Rml bool) -> Rml -> Rml -> Rml *)
(* | App_stm : forall {B}, B -> @Rml (B -> A) -> @Rml B -> Rml. *)

Inductive allType :=
| Error : string -> allType
| Bool : bool -> allType
| Value : forall {A}, A -> allType.

Inductive Rml :=
| Var : nat -> Rml
| Const : allType -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
| Fun_stm : nat -> allType -> Rml -> Rml
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.

Definition prob_unit {R} {A} (x : A) := @unit (probability_monad_type R) (probability_monad R) A x.
Definition prob_bind {R} {A B} mu M:= @bind (probability_monad_type R) (probability_monad R) A B mu M.

(* Definition Mif {R : realType} {A} (mu_b : (bool -> R) -> R) (mu1 : (A -> R) -> R) (mu2 : (A -> R) -> R) : (A -> R) -> R := *)
(*   @prob_bind R bool A mu_b (fun b => if b then mu1 else mu2). *)

Definition doIf {R} x (mu1 : (allType -> R) -> R) (mu2 : (allType -> R) -> R) :=
  match x with
  | Bool _ => mu1
  | _ => mu2
  end.
  
Definition Mif {R : realType} (mu_b : (allType -> R) -> R) (mu1 : (allType -> R) -> R) (mu2 : (allType -> R) -> R) : (allType -> R) -> R :=
  @prob_bind R allType allType mu_b (fun x => doIf x mu1 mu2).

Fixpoint lookup (l : seq (nat * allType)) (s : nat) : allType :=
  match l with
  | (s',v) :: r =>
    if s == s'
    then v
    else lookup r s
  | _ => (Error "No var of given name")
  end.

Check @lookup.

Fixpoint interp {R : realType} (x : Rml) (l : seq (nat * allType)) : probability_monad_type R allType :=
  match x with
  | Var s => prob_unit (lookup l s)
  | Const v => prob_unit v
  | Fun_stm x sigma t => (* TODO: unit *) interp t ((x,sigma) :: l)
  | Let_stm x a b => prob_bind (interp a l) (fun v => interp b ((x, v) :: l))
  | If_stm b a1 a2 => Mif (interp b l) (interp a1 l) (interp a2 l)
  | App_stm e1 e2 => bind (interp e1 l) (fun v => interp e1 ((0%nat,v) :: l)) (* TODO: ORDERING? *)
                         (* TODO: replace 0 with correct index *)
  end.

Definition std_interp {R} (r : Rml) := @interp R (r) nil.
Definition rml_let_example := Let_stm (0%nat) (Const (Value 2%nat)) (Var (0%nat)). (* = Let x = 2 In x *)
                                      
Compute std_interp rml_let_example. (* = unit 2 *)  

Check expr_.
Check ivar.

Definition vars_to_nat (t : inhabited.Inhabited.type) (v : (vars_ ident) t) : nat :=
  0. (* TODO *)

Check @iexpr.

Inductive expr_typed {A} :=
| exp : forall {B}, expr B -> option A -> expr_typed.

Definition value_of_expr {A : Type} (e : expr A) : expr_typed :=
  match e with
  | cst_ t c => exp e (Some c)
  | _ => exp e None
  end.

Fixpoint translate_exp_bexp (e : @expr_typed bool) : Rml := (* inhabited.Inhabited.type *) (* (inhabited.Inhabited.sort t) *)
  match e with
  | exp B e c =>
    match e with
    | var_ t x => Const (Error "")
    | cst_ _ _ => Const (Bool (match c with
                              | Some b => b
                              | _ => false
                              end))
    | prp_ pm => Const (Error "")
    | app_ _ _ f x => Const (Error "")
    end
  end.

Fixpoint translate_exp {A : Type} (e : @expr A) : Rml := (* inhabited.Inhabited.type *) (* (inhabited.Inhabited.sort t) *)
  match e with
  | var_ t x => Var (vars_to_nat t x)
  | cst_ t c => Const (Value c) (* (Some c) *)
  | prp_ pm => Const (Error "TODO") (* default *) (* TODO *)
  | app_ _ _ f x => App_stm (translate_exp f) (translate_exp x)
  end.

Fixpoint pwhile_to_rml {R : realType} (x : cmd_ _ cmem) : Rml :=
  match x with

  | seqc (assign t v e) e0 => (Let_stm (vars_to_nat t v) (translate_exp e) (@pwhile_to_rml R e0))
    
  | abort => (Const (Error "Abort"))
  | skip => (Const (Error "Skip"))
  | assign t v e => (Let_stm (vars_to_nat t v) (translate_exp e) (Var (vars_to_nat t v))) (* This does not seem to be correct behavior *)
  | cond e c c0 => (If_stm (translate_exp_bexp (value_of_expr e)) (@pwhile_to_rml R c) (@pwhile_to_rml R c0))
  | while _ _ => (Const (Error "TODO WHILE LOOP"))
  | pwhile.random _ _ _ => (Const (Error "TODO RANDOM"))
  | seqc e e0 => (App_stm (@pwhile_to_rml R e) (@pwhile_to_rml R e0))
  end.

Example example_pwhile_program_assignment :
  forall (R : realType) (x : vars nat_ihbType),
    @pwhile_to_rml R (x <<- 2%:S)%S = Let_stm 0 (Const (Value 2)) (Var 0).
Proof. intros ; simpl. reflexivity. Qed.

Example example_pwhile_program_if_boolean_condition :
  forall R (b : bool),
    @pwhile_to_rml R (cond (cst_ b) skip skip) = If_stm (Const (Bool b)) (Const (Error "Skip")) (Const (Error "Skip")).
Proof. intros ; simpl. reflexivity. Qed.
