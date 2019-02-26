Require Import String.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.altreals.distr.
From mathcomp Require Import analysis.reals.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.
Require Import FunctionalExtensionality.

Check cst_ 2.

Parameter R : nat.  (* override from pwhile, variables still in scope? *)

(* -------------------------------------------------------------------------------- *)

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

Definition expectation_monad_type (R : realType) := continuation_monad_type R.
Instance expectation_monad (R : realType) : Monad (expectation_monad_type R) := continuation_monad R.

Inductive error {E A} :=
| Throw (_ : E) : @error E A
| Return (_ : A) : @error E A.

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
  }.
Proof.
  all: try (intros ; apply functional_extensionality ; intros ; reflexivity).    
  - intros.
    apply functional_extensionality.
    intros.
    assert ((fun x1 : error => match x1 with | Throw a => x0 (Throw a) | Return a => punit (Return a) x0 end) = x0) by (apply functional_extensionality ; (destruct x1 ; reflexivity)).
    rewrite H ; clear H.
    reflexivity.
Qed.

Instance option_monad : Monad option :=
  {
    unit := @Some ;
    bind _ _ x f :=
      match x with
      | Some y => f y
      | None => None
      end
  }.
Proof.
  all: try destruct x.
  all: reflexivity.
Qed.

Definition ounit {A} := @unit (option) (option_monad) A.
Definition obind {A B} := @bind (option) (option_monad) A B.
    
(* -------------------------------------------------------------------------------- *)

Inductive Rml {E A} : Type :=
| Var : nat -> Rml
| Const : @error E A -> Rml
| Let_stm {B} : nat -> @Rml E B -> @Rml E A -> Rml
| Fun_stm : nat -> @error E A -> @Rml E A -> Rml
| If_stm : forall B, @Rml bool B -> @Rml E A -> @Rml E A -> @Rml E A
| App_stm {B} : @Rml E (B -> A) -> @Rml E B -> Rml.

(* -------------------------------------------------------------------------------- *)

Definition Mif {E A B} {R : realType} (mu_b : (@error bool B -> R) -> R) (mu1 : (@error E A -> R) -> R) (mu2 : (@error E A -> R) -> R) (f : E) : (@error E A -> R) -> R :=
  pbind mu_b
        (fun x =>
           match x with
           | Throw b => if b then mu1 else mu2
           | Return y => punit (Throw f)
           end).

Inductive A_list {E} {A : list Set} :=
| mlCons : forall {B : Set}, @error E (head B A) -> @A_list E (behead A) -> A_list
| mlNil : A_list.

Definition mlCons' {E} {A : list Set} {B : Set} (e : @error E B) (l : @A_list E A) := @mlCons E (B :: A) B e l.

Theorem list_keeps_type :
  forall E (B : Set) (n : nat) (e : @error E B),
  forall (A : list Set) (l : @A_list E A),
    match (@mlCons E (B :: A) B e l) with
    | mlCons _ e' l' => e = e' /\ l = l'
    | mlNil => False 
    end.
Proof.
  all: repeat split.
Qed.  

Inductive is_well_formatted {E} : forall {A : list Set}, @A_list E A -> Prop :=
| A_list_empty : @is_well_formatted E nil mlNil
| A_list_cons : forall A (l : @A_list E (behead A)) B (e : @error E (head B A)),
    (B = head B A) -> @is_well_formatted E (behead A) l -> is_well_formatted (@mlCons E A _ e l).

Fixpoint check_well_formatted {E} {A : list Set} (l : @A_list E A) : bool :=
  match l with
  | mlCons B p l' => @check_well_formatted E (behead A) l'
  | mlNil =>
    match A with
    | nil => true
    | _ => false
    end
  end.

Theorem well_formated_if_checked :
  forall E A,
  forall (l : @A_list E (behead A)),
    check_well_formatted l = true <-> @is_well_formatted E (behead A) l.
Proof. Admitted. (* TODO *)

(* Check (fun A LA s => (fun B : @nth Set A LA s => (fun (x : B) => x))). *)

(* Fixpoint lookup0 {E} {A : Set} {R : realType} {LA} (l : @A_list E (A :: LA)) `{_ : is_well_formatted l} : E -> @error E (@nth Set A (A :: LA) 0) := *)
(*   (fun err => *)
(*      match l with *)
(*      | mlCons B b n => b *)
(*      | mlNil => Throw err *)
(*      end). *)
Definition tail {E} {R : realType} {LA} (l : @A_list E LA) : @A_list E (behead LA) :=
  match l with
  | mlCons _ _ n => n
  | mlNil => mlNil
  end.

Fixpoint behead_n_times {T} LA n :=
  match n with
  | O => LA
  | S n' => @behead T (behead_n_times LA n')
  end.

Fixpoint tail_n_times {E} {R : realType} {LA} (l : @A_list E LA) n : @A_list E (behead_n_times LA n) :=
  match n with
  | O => l
  | S n' => @tail E R (behead_n_times LA n') (@tail_n_times E R LA l n')
  end.

Compute tail_n_times (@mlNil _ nil) 3.
Compute tail_n_times (mlCons' (Return 4) (@mlNil _ nil)) 0.
Compute tail_n_times (mlCons' (Return 4) (@mlNil _ nil)) 1.

Definition ss {T} := (mlCons' (Return 4) (mlCons' (Return 4) (@mlNil T nil))).
Check ss.
Definition asdf {T R K} (s : A_list) := (fun n => @tail_n_times T R K s n).

Inductive correct_index {E LA} : @A_list E LA -> nat -> Prop :=
| zero : forall l n, n < size LA -> correct_index l n.

Fixpoint check_correct_index {E} {LA : list Set} (l : @A_list E LA) (s : nat) : bool :=
  s < size LA.

Compute check_correct_index (@mlNil _ nil) 0.

Theorem behead_is_list_if_index_correct :
  forall LA E,
  forall (l : @A_list E LA) (s : nat),
    is_well_formatted l -> correct_index l s -> exists k m, behead_n_times LA s = k :: m.
Proof.
  induction LA ; intros.
  + inversion H0.
    subst.
    simpl in *.
    easy.
  + induction s.
    * simpl.
      exists a.
      exists LA.
      reflexivity.
    * simpl.
      Check @behead.
      Check @behead_n_times.
      assert (forall T a LA s, @behead T (@behead_n_times T (a :: LA) s) = behead_n_times (LA) s).
      -- induction s0.
         ++ intros.
            reflexivity.
         ++ simpl.
            rewrite IHs0.
            reflexivity.
      -- rewrite H1.
         destruct l.
         ++ inversion H ; subst.
            apply (IHLA E l0).
            ** assumption.
            ** inversion H0 ; subst.
               apply zero.
               simpl in H2.
               apply H2.
         ++ easy.
Qed.

(* Fixpoint lookup0 {E} {R : realType} {P} {LA} `{_ : forall s, exists k m, (@behead_n_times Set LA s) = (k :: m)} (l : @A_list E (P :: LA)) `{_ : is_well_formatted l} : E -> @error E P := *)
(*   (fun err => *)
(*      match l with *)
(*      | mlCons B b n => b *)
(*      | mlNil => Throw err *)
(*      end). *)


Fixpoint lookup0 {E} {R : realType} {P} {LA} (l : @A_list E (P :: LA)) `{_ : is_well_formatted l} : E -> @error E P :=
  (fun err =>
     match l with
     | mlCons B b n => b
     | mlNil => Throw err
     end).

Compute lookup0 (tail_n_times (mlCons' (Return 4) (@mlNil _ nil)) 0) true.
Compute lookup0 (asdf ss 1) false.

Definition convert {E LA s}  (f : @A_list E (@behead_n_times Set LA s)) {k m} `{_ : @behead_n_times Set LA s = (k :: m)} : @A_list E (k :: m).
  rewrite H in f.
  apply f.
Qed.  

Fixpoint lookup {E} {A : Set} {R : realType} {LA} (l : @A_list E LA) (s : nat) `{_ : is_well_formatted l} `{_ : correct_index l s} : E -> @error E (@nth Set A LA s).
Proof.
  intros err.
  pose (correct_index_value := @tail_n_times E R LA l s).
  pose (behead_is_list_if_index_correct LA E l s is_well_formatted0 correct_index0).

  Check @lookup0 E R A _ (convert correct_index_value).
  Check @lookup0 E R A _ (convert correct_index_value).

  Check @is_well_formatted E _ (@convert _ _ _ correct_index_value _ _ _).

  Check @convert.
  Check nth A LA s.
  assert (behead_val : behead_n_times LA s = nth A LA s :: (behead_n_times LA s.+1)).
  - simpl.
    generalize dependent s.
    generalize dependent l.
    induction LA.
    + inversion correct_index0 ; subst.
      easy.
    + simpl in *.
      assert (forall s, behead (behead_n_times (a :: LA) s) = behead_n_times LA s).
      -- induction s.
         ++ reflexivity.
         ++ simpl.
            rewrite IHs.
            reflexivity.
      -- induction s.
         ++ intros.
            reflexivity.
         ++ intros.
            simpl.
            destruct LA.
            ** inversion correct_index0 ; subst.
               simpl in *.
               easy.
            ** rewrite H.
               inversion is_well_formatted0 ; subst.
               inversion correct_index0 ; subst.

               Check IHLA l0 (H3) s (zero l0 s _).
               Check zero l0 s _.
               
               Check IHLA l0 (H3) s (zero l0 s _).
               apply (IHLA l0 (H3) s).
               apply zero.
               simpl.
               apply H2.
  - (* Set Printing All. *)
    Check correct_index_value.
    pose (converted := (@convert E LA s correct_index_value (nth A LA s) (behead_n_times LA s.+1))).

    Check converted behead_val.
    pose (converted' := converted behead_val).
    
    Check @lookup0 E R (@nth Set A LA s) _ converted' _ _.
    Check (fun h1 h2 h3 => @lookup0 E R (@nth Set A LA s) (@behead_n_times Set LA s.+1) converted' h2 h3).
    pose (solution := (fun h2 => @lookup0 E R (@nth Set A LA s) (@behead_n_times Set LA s.+1) converted' h2 err)).
    
    apply solution.

    unfold converted'.
    unfold converted.
    unfold correct_index_value.

    destruct s.
    + simpl.

      clear solution.
      clear converted'.
      clear converted.
      clear e.
      clear correct_index_value.
      clear err.
      clear correct_index0.
      
      pose (l'' := (@convert E LA O l
                             match LA return Set with
                             | nil => A
                             | cons x _ => x
                             end (@behead Set LA) behead_val)).

      (* Set Printing All. *)
      
      destruct LA.
      * simpl.
        easy.
      + destruct l.
        
      
      
      (* TODO WORK HERE *)


      

      
      apply is_well_formatted0.
      destruct (convert _) eqn : oldl.
      * inversion is_well_formatted0 ; subst.
    
    destruct l.
    + Check @A_list_cons E LA l _ .
      apply A_list_cons.
    
    apply (@lookup0 E R (@nth Set A LA s) _ _ (@convert E LA s correct_index_value (nth A LA s) (behead_n_times LA s.+1) _)).
  apply (@lookup0 E R (@nth Set A LA s) _ _ (convert correct_index_value)).

Fixpoint lookup0 {E} {R : realType} {P} {LA} `{_ : forall s, exists k m, (@behead_n_times Set LA s) 
  
  
  (* exists *)
  assert (forall k m, forall (p : behead_n_times LA s = k :: m), @is_well_formatted _ _ (@convert _ _ _ correct_index_value _ _ p)).
  - intros.
    destruct (convert correct_index_value).
    + apply A_list_cons.
      simpl.
    
  apply (@lookup0 E R A _ _ (convert correct_index_value)).
  Check @lookup0 E R A _ _ (correct_index_value).
    
  :=
  (fun err =>
     lookup0 (tail_n_times l s) err
  ).

Theorem correct_lookup :
  forall E LA,
  forall (l : @A_list E LA),
  forall n
    correct_index l n -> lookup0 (asdf l n) false.

Compute lookup0 (asdf ss 2) false.

Fixpoint lookup {E} {A : Set} {R : realType} {LA} (l : @A_list E LA) (s : nat) `{_ : is_well_formatted l} : E -> @error E (@nth Set A LA s) :=
  (fun err =>
     lookup0 (tail_n_times l s) err
  ).

Fixpoint lookup {E} {A : Set} {R : realType} {LA} (l : @A_list E LA) (s : nat) `{_ : is_well_formatted l} : E -> @error E (@nth Set A LA s) :=
  (fun err =>
     match s with
     | O => 
       match l with
       | mlCons B b n => b
       | mlNil => Throw err
       end
     end).

Fixpoint lookup {E} {A : Set} {R : realType} {LA} (l : @A_list E LA) (s : nat) : E -> @error E (@nth Set A LA s) :=
  (fun err =>
     match l with
     | mlCons B (a,b) n =>
       if (s == a)
       then b (* b *) (* <-- Problem here *)
       else @lookup E A R (behead LA) n (s-1) err
     | mlNil => Throw err
     end
   ).


Fixpoint lookup {R : realType} (l : A_list) (s : nat) : forall E A, E -> @error E A :=
  (fun E A => 
     (fun err =>
        match l with
        | mlCons B (a,b) n =>
          if (s == a)
          then b (* b *) (* <-- Problem here *)
          else @lookup R n s E A err
        | mlNil => Throw err
        end
     )).

(* -------------------------------------------------------------------------------- *)

Fixpoint interp {E A} {R : realType} (x : @Rml E A) (l : A_list) (err : E) : (@error E A -> R) -> R :=
  match x with
  | Var s => punit (@lookup E A R l s err)
  | Const v => punit v (* = string T *)
  | Fun_stm x sigma t =>
    (* TODO: unit *)
    interp t (mlCons (x,unit sigma) l) err
  | Let_stm T x a b =>
    pbind (interp a l err) (fun v =>
       interp b (@mlCons E T (x, v) l) err)
  | If_stm B b a1 a2 => Mif (@interp bool B R b l true) (interp a1 l err) (interp a2 l err) err
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

(* -------------------------------------------------------------------------------- *)

Example interp_if_stm :
  forall R B b s,
    @interp nat nat R (If_stm B (Const (bthrow b)) (Const (Return 0)) (Const (Return 0))) mlNil s = punit (Return 0).
Proof.
  intros.  
  simpl.
  unfold Mif.
  unfold pbind.
  unfold punit.
  simpl.
  destruct b ; reflexivity.
Qed.

Example interp_lookup_var :
  forall R s n,
    @interp nat nat R (Let_stm n (Const (Return 3)) (Var n)) mlNil s = punit (Return 3).
Proof.
  intros.
  simpl.
  unfold pbind.
  unfold punit.
  simpl.
Qed.

Definition std_interp {R} {A E} (r : Rml) := @interp A E R (r) mlNil.

Check @Let_stm.

Definition rml_let_example {E} := @Let_stm E nat nat (0%nat) (Const (Return 2%nat)) (Var (0%nat)). (* = Let x = 2 In x *)
                                      
Compute std_interp rml_let_example. (* = unit 2 *)  

Check expr_.
Check ivar.

(* -------------------------------------------------------------------------------- *)

Definition vars_to_nat (t : inhabited.Inhabited.type) (v : (vars_ ident) t) : nat :=
  1. (* TODO *)

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
    | var_ t x => Const (@breturn string EmptyString)
    | cst_ _ _ => Const (bthrow (match c with
                                | Some b => b
                                | _ => false
                                end))
    | prp_ pm => Const (@breturn string EmptyString)
    | app_ _ _ f x => Const (@breturn string EmptyString)
    end
  end.

(** Return value is saved in Var 0 *)

Fixpoint translate_exp {E A : Type} (e : @expr A) : @Rml E A := (* inhabited.Inhabited.type *) (* (inhabited.Inhabited.sort t) *)
  match e with
  | var_ t x => Var (vars_to_nat t x)
  | cst_ t c => Const (Return c) (* (Some c) *)
  | prp_ pm => Const (Return true) (* TODO *)
  | app_ T U f x => App_stm (@translate_exp E (T -> U) f) (translate_exp x)
  end.

(* -------------------------------------------------------------------------------- *)

Fixpoint pwhile_to_rml {E A} {R : realType} (x : cmd) : @Rml E A :=
  match x with

  | seqc (assign t v e) e0 =>
    Let_stm (vars_to_nat t v) (translate_exp e) (@pwhile_to_rml E A R e0)
                                     
  | abort => Var 0 (* Const (sthrow "Abort") *)
  | skip => Var 0 (* Const (sthrow "Skip") *)
  | assign t v e =>
    Let_stm
      (vars_to_nat t v)
      (translate_exp e)
      (Var 0) (* (Var (vars_to_nat t v)) *)
  (* This does not seem to be correct behavior *)
  | cond e c c0 =>
    If_stm
      _
      (translate_exp_bexp (value_of_expr e))
      (@pwhile_to_rml E A R c)
      (@pwhile_to_rml E A R c0)
  | while _ _ => Var 0 (* Const (sthrow "TODO WHILE LOOP") *)
  | pwhile.random _ _ _ => Var 0 (* Const (sthrow "TODO RANDOM") *)
  | seqc e e0 => App_stm (@pwhile_to_rml E _ R e) (@pwhile_to_rml E A R e0)
                        (* Should this not be a let statement instead of sequence? *)
  end.

(* -------------------------------------------------------------------------------- *)

Example example_pwhile_program_assignment :
  forall E A (R : realType) (x : vars nat_ihbType),
    @pwhile_to_rml E A R (x <<- 2%:S)%S = Let_stm (vars_to_nat _ x) (Const (Return 2)) (Var 0).
Proof. intros ; simpl. reflexivity. Qed.

Example example_pwhile_program_if_boolean_condition :
  forall A R (b : bool),
    @pwhile_to_rml string A R (cond (cst_ b) skip skip) =
    If_stm string (Const (bthrow b)) (Var 0) (Var 0).
Proof. intros ; simpl. reflexivity. Qed.

(* -------------------------------------------------------------------------------- *)

Compute (fun E A R n => interp (@pwhile_to_rml string A R (n <<- 2%:S)%S) mlNil).

Section Examples.
Context (ident : eqType) (t : ihbType) (x : (vars_ ident) t).

Compute var_.
Compute @ivar nat_eqType nat_eqType id nat_ihbType.
Compute @var_ _ _ _ x%V.

End Examples.