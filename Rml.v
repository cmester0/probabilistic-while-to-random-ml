Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.
Require Import FunctionalExtensionality.

Check cst_ 2.

Parameter R : nat.  (* override from pwhile, variables still in scope? *)

Reserved Notation "x >>= f" (at level 40, left associativity).
Class Monad (M : Type -> Type) := {
  unit : forall {A}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
    where "x >>= f" := (bind x f);
  monad_law_unit_l : forall {A B} (a : A) (k : A -> M B), unit a >>= k = k a;
  monad_law_unit_r : forall {A} (x : M A), x >>= unit = x;
  monad_law_assoc : forall {A B C} (x : M A) (k : A -> M B) (h : B -> M C),
      x >>= (fun a => k a >>= h) = x >>= k >>= h
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

Inductive error {E A} :=
| Throw : E -> error
| Return : A -> error.

(* Inductive isBool {T} := *)
(* | Bool : bool -> isBool *)
(* | NBool : T -> isBool. *)

Instance error_monad E : Monad (@error E) :=
  {
    unit _ x := Return x ;
    bind _ _ x f :=
      match x with
      | Return y => f y
      | Throw y => Throw y
      end
  }.
Proof. all: try destruct x. all: reflexivity. Qed.

(* Inductive allType := *)
(* | Error : string -> allType *)
(* | Bool : bool -> allType *)
(* | Value : forall {A}, A -> allType. *)

Instance notBool_monad : Monad (@error bool) := error_monad bool.
Instance string_env_error_monad : Monad (@error string) := error_monad string.

(* Inductive allType := *)
(* | Error : string -> allType *)
(* | Bool : bool -> allType *)
(* | Value : forall {A}, A -> allType. *)

(* Inductive Rml {T : Type} := *)
(* | Var : nat -> Rml *)
(* | Const : (forall A, @error string A) -> Rml *)
(* | Let_stm : nat -> Rml -> Rml -> Rml *)
(* | Fun_stm : nat -> (forall A, @error string A) -> Rml -> Rml *)
(* | If_stm : (@Rml bool) -> (@Rml T) -> (@Rml T) -> (@Rml T) *)
(* | App_stm : Rml -> Rml -> Rml. *)

Inductive Rml {E A} :=
| Var : nat -> Rml
| Const : @error E A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
| Fun_stm : nat -> @error E A -> Rml -> Rml
| If_stm : @Rml bool A -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.


Check (fun {R A mu_b} => @bind (probability_monad_type R) (probability_monad R) (@error bool A) (@error string A) mu_b).

Definition punit {R} {A} := @unit (probability_monad_type R) (probability_monad R) A.
Definition pbind {R} {A B} := @bind (probability_monad_type R) (probability_monad R) A B.

Definition sthrow {A} := @Throw string A.
Definition sreturn {A} := @Return string A.

Definition bthrow {A} := @Throw bool A.
Definition breturn {A} := @Return bool A.

(* Definition Mif {A} {R : realType} (mu_b : (@error bool A -> R) -> R) (mu1 : (@error string A -> R) -> R) (mu2 : (@error string A -> R) -> R) : (@error string A -> R) -> R := *)
(*   pbind mu_b *)
(*         (fun x => *)
(*            match x with *)
(*            | Throw b => if b then mu1 else mu2 *)
(*            | Return y => punit (sthrow "Condition not bool") *)
(*            end). *)

Definition Mif {A E} {R : realType} (mu_b : (@error bool A -> R) -> R) (mu1 : (@error E A -> R) -> R) (mu2 : (@error E A -> R) -> R) (f : E) : (@error E A -> R) -> R :=
  pbind mu_b
        (fun x =>
           match x with
           | Throw b => if b then mu1 else mu2
           | Return y => punit (Throw f)
           end).

Definition reader T := forall E, E -> T.

Instance reader_monad : Monad reader :=
  {
    unit _ x := (fun E => fun (e : E) => x);
    bind _ _ m f := fun T => fun (e : T) => f (m T e) T e
  }.
Proof. all: reflexivity. Qed.

Check @unit reader reader_monad nat.
Compute @bind reader reader_monad .

Inductive A_elem :=
| elem : forall {A E}, @error E A -> A_elem.

Inductive nat_A_list :=
| mlCons : forall {A E}, (nat * @error E A) -> nat_A_list -> nat_A_list
| mlNil : nat_A_list.

(* seq (nat * (@error string A) *)

Fixpoint lookup {A E} {R : realType} (l : nat_A_list) (s : nat) : @error E A.
Proof. Admitted.

Check @lookup.

(* @error string A *)

Fixpoint interp {A E} {R : realType} (x : Rml) (l : nat_A_list) (err : E) : (@error E A -> R) -> R :=
  match x with
  | Var s => punit (@lookup A E R l s)
  | Const v => punit v (* = string T *)
  | Fun_stm x sigma t =>
    (* TODO: unit *)
    interp t (mlCons (x,unit sigma) l) err
  | Let_stm x a b =>
    pbind (interp a l err) (fun v =>
       interp b (@mlCons A E (x, v) l) err)
  | If_stm b a1 a2 => Mif (@interp A bool R b l true) (interp a1 l err) (interp a2 l err) err
  (* TODO: find default, true? *)
  (* variables cannot be booleans *)
  | App_stm e1 e2 => pbind (interp e1 l err) (fun v => interp e1 (mlCons (0%nat,v) l) err)
                         (* TODO: ORDERING? *)
                         (* TODO: replace 0 with correct index *)
  end.

Example interp_if_stm :
  forall R b s,
    @interp nat string R (If_stm (Const (bthrow b)) (Const (Return 0)) (Const (Return 0))) mlNil s = punit (Return 0).
Proof.
  intros.  
  simpl.
  unfold Mif.
  unfold pbind.
  unfold punit.
  simpl.
  destruct b ; reflexivity.
Qed.

Definition std_interp {R} {A E} (r : Rml) := @interp A E R (r) mlNil.

Check @Let_stm.

Definition rml_let_example {E} := @Let_stm E nat (0%nat) (Const (Return 2%nat)) (Var (0%nat)). (* = Let x = 2 In x *)
                                      
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

(* Fixpoint translate_exp_bexp (e : @expr_typed bool) : Rml := (* inhabited.Inhabited.type *) (* (inhabited.Inhabited.sort t) *) *)
(*   match e with *)
(*   | exp B e c => *)
(*     match e with *)
(*     | var_ t x => Const (breturn e) *)
(*     | cst_ _ _ => Const (bthrow (match c with *)
(*                               | Some b => b *)
(*                               | _ => false *)
(*                               end)) *)
(*     | prp_ pm => Const (sthrow "") *)
(*     | app_ _ _ f x => Const (sthrow "") *)
(*     end *)
(*   end. *)

Fixpoint translate_exp {A : Type} (e : @expr A) : Rml := (* inhabited.Inhabited.type *) (* (inhabited.Inhabited.sort t) *)
  match e with
  | var_ t x => Var (vars_to_nat t x)
  | cst_ t c => Const (Return c) (* (Some c) *)
  | prp_ pm => Const (sthrow "TODO") (* default *) (* TODO *)
  | app_ _ _ f x => App_stm (translate_exp f) (translate_exp x)
  end.

Fixpoint pwhile_to_rml {R : realType} (x : cmd_ _ cmem) : Rml :=
  match x with

  | seqc (assign t v e) e0 => (Let_stm (vars_to_nat t v) (translate_exp e) (@pwhile_to_rml R e0))
    
  | abort => (Const (Error "Abort"))
  | skip => (Const (Error "Skip"))
  | assign t v e =>
    Let_stm
      (vars_to_nat t v)
      (translate_exp e)
      (Var (vars_to_nat t v))
  (* This does not seem to be correct behavior *)
  | cond e c c0 =>
    If_stm
      (translate_exp_bexp (value_of_expr e))
      (@pwhile_to_rml R c)
      (@pwhile_to_rml R c0)
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