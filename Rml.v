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

Definition expectation_monad_type (R : realType) := continuation_monad_type R.
Instance expectation_monad (R : realType) : Monad (expectation_monad_type R) := continuation_monad R.

Inductive error {E A} :=
| Throw : E -> error
| Return : A -> error.

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

Instance notBool_monad : Monad (@error bool) := error_monad bool.
Instance string_env_error_monad : Monad (@error string) := error_monad string.

Definition punit {R} {A} := @unit (expectation_monad_type R) (expectation_monad R) A.
Definition pbind {R} {A B} := @bind (expectation_monad_type R) (expectation_monad R) A B.

Definition sthrow {A} := @Throw string A.
Definition sreturn {A} := @Return string A.

Definition bthrow {A} := @Throw bool A.
Definition breturn {A} := @Return bool A.

(* Set Printing All. *)

Instance expectation_error_monad {R : realType} E : Monad (fun A => (@error E A -> R) -> R) :=
  {
    unit A x := punit (Return x) ;
    bind {A B} mu M :=
      (fun f =>
         mu (fun x =>
               (match x with
                | Throw a => f (@Throw E B a)
                | Return a => M a f
                end)
      ))
        (* mu (fun x => M (bind x f)) *)
  }.
Proof.
  - intros A B a M.
    apply functional_extensionality.
    intros f.
    Check (fun x => punit (Return a) x).
    assert ((match (Return a) with
            | Throw a0 => f (Throw a0)
            | Return a0 => M a0 f
                  end = M a f)).
    + reflexivity.
    + assert (forall A (a : A) (f : A -> R), @punit R A a f = f a).
      * reflexivity.
      * rewrite H0.
        reflexivity.
  
  - intros.
    apply functional_extensionality.
    intros.
    assert ((fun x1 : error => match x1 with | Throw a => x0 (Throw a) | Return a => punit (Return a) x0 end) = x0) by (apply functional_extensionality ; (destruct x1 ; reflexivity)).
    rewrite H ; clear H.
    reflexivity.

  - intros.
    apply functional_extensionality.
    intros.
    reflexivity.
Qed.
    
  
Inductive Rml {E A} :=
| Var : nat -> Rml
| Const : @error E A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
| Fun_stm : nat -> @error E A -> Rml -> Rml
| If_stm : @Rml bool A -> Rml -> Rml -> Rml
| App_stm : forall B, @Rml E (B -> A) -> @Rml E B -> @Rml E A.

Definition Mif {E A} {R : realType} (mu_b : (@error bool A -> R) -> R) (mu1 : (@error E A -> R) -> R) (mu2 : (@error E A -> R) -> R) (f : E) : (@error E A -> R) -> R :=
  pbind mu_b
        (fun x =>
           match x with
           | Throw b => if b then mu1 else mu2
           | Return y => punit (Throw f)
           end).

Inductive A_elem :=
| elem : forall {A E}, @error E A -> A_elem.

Inductive nat_A_list :=
| mlCons : forall {A E}, (nat * @error E A) -> nat_A_list -> nat_A_list
| mlNil : nat_A_list.

(* seq (nat * (@error string A) *)

Fixpoint lookup {A E} {R : realType} (l : nat_A_list) (s : nat) : @error E A.
Proof. Admitted.

Set Printing All.

Fixpoint interp {E A} {R : realType} (x : Rml) (l : nat_A_list) (err : E) : (@error E A -> R) -> R :=
  match x with
  | Var s => punit (@lookup A E R l s)
  | Const v => punit v (* = string T *)
  | Fun_stm x sigma t =>
    (* TODO: unit *)
    interp t (mlCons (x,unit sigma) l) err
  | Let_stm x a b =>
    pbind (interp a l err) (fun v =>
       interp b (@mlCons A E (x, v) l) err)
  | If_stm b a1 a2 => Mif (@interp bool A R b l true) (interp a1 l err) (interp a2 l err) err
  (* TODO: find default, true? *)
  (* variables cannot be booleans *)
  | App_stm B e1 e2 =>
    pbind (interp e1 l err)
          (fun (v : @error E (B -> A)) =>
             match v with
             | Throw f => unit (@Throw E A f)
             | Return f => (* f : B -> A *)
               pbind (interp e2 (mlCons (0%nat,v) l) err)
                     (fun k =>
                        match k with
                        | Return a => unit (unit (f a)) (* a : B *)
                        | Throw a => unit (@Throw E A a) (* a : E *)
                        end)
             end)
          (* Continuation error monad *)
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