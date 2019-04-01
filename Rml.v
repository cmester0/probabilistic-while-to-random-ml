From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.reals.
From mathcomp.analysis Require Import boolp reals distr.
From Hammer Require Import Hammer.

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
Notation "x >>= f" := (bind x f).
         
(* -------------------------------------------------------------------------------- *)

Definition continuation_monad_type := fun ZO A => (A -> ZO) -> ZO.
Instance continuation_monad {ZO} : Monad (continuation_monad_type ZO) :=
  {
    unit := fun {A} (x : A) => @^~ x ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

(* -------------------------------------------------------------------------------- *)

Inductive Rml {n : nat} : Type :=
| Var : (nat * Type) -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : n > 0 -> (nat * Type) -> Rml -> Rml -> Rml
(* | Fun_stm : forall B, (nat * Type) -> B -> Rml -> Rml *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed {n : nat} : seq (nat * Type) -> @Rml n -> Prop :=
| well_var : forall A x l, List.In (x,A) l -> well_formed l (Var (x,A))
| well_const : forall A c l, well_formed l (Const A c)
| well_let_stm : forall x e1 e2 l {gz : n > 0}, well_formed l e1 -> well_formed (x :: l) e2 -> well_formed l (Let_stm gz x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Locate "/\".

(* Fixpoint lookup (env : seq (nat * Type * @Rml 0)) p : List.In p (map fst env) -> @Rml 0. *)
(* Proof. *)
(*   case env. *)
(*   - intros. *)
(*     contradiction. *)
(*   - intros. *)
(*     destruct (pselect (p0.1 = p)). *)
(*     + refine p0.2. *)
(*     + assert (List.In p [seq i.1 | i <- l]) by (inversion H ; easy). *)
(*       refine (lookup l p H0). *)
(* Defined. *)
    
Fixpoint lookup (env : seq (nat * Type * @Rml 0)) p : @Rml 0 :=
  match env with
  | [::] => (Const nat 4) (* Should not happen *)
  | y :: ys =>
    if pselect (y.1 = p)
    then y.2
    else lookup ys p
  end.

Fixpoint replace_all_variables_aux {n : nat} (x : @Rml n) (env : seq (nat * Type * @Rml 0)) {x_well : well_formed (map fst env) x} : @Rml 0.
Proof.
  destruct x.
  - apply (lookup env p).
    (* inversion x_well ; subst. *)
    (* assumption. *)
  - refine (Const A a).
  - assert (a'_well : well_formed [seq i.1 | i <- env] x1) by (inversion x_well ; assumption).
    pose (a' := replace_all_variables_aux n x1 env a'_well).
    
    assert (b_well : well_formed [seq i.1 | i <- (p, a') :: env] x2) by (inversion x_well ; assumption).
    
    refine (replace_all_variables_aux n x2 ((p,a') :: env) b_well).
  - assert (b'_well : well_formed [seq i.1 | i <- env] x1) by (inversion x_well ; assumption).
    assert (m1'_well : well_formed [seq i.1 | i <- env] x2) by (inversion x_well ; assumption).
    assert (m2'_well : well_formed [seq i.1 | i <- env] x3) by (inversion x_well ; assumption).
    
    pose (b' := replace_all_variables_aux n x1 env b'_well).
    pose (m1' := replace_all_variables_aux n x2 env m1'_well).
    pose (m2' := replace_all_variables_aux n x3 env m2'_well).
    refine (If_stm b' m1' m2').

  - assert (e1'_well : well_formed [seq i.1 | i <- env] x1) by (inversion x_well ; assumption).
    assert (e2'_well : well_formed [seq i.1 | i <- env] x2) by (inversion x_well ; assumption).
    
    pose (e1' := replace_all_variables_aux n x1 env e1'_well).
    pose (e2' := replace_all_variables_aux n x2 env e2'_well).
    refine (App_stm T e1' e2').
Defined.    

Definition replace_all_variables {n : nat} (x : @Rml n) `{x_well : well_formed nil x} : @Rml 0 :=
  @replace_all_variables_aux n x nil x_well.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type {n : nat} : Type -> @Rml n -> seq (nat * Type) -> Prop :=
| valid_var : forall x l A, List.In (x,A) l -> rml_valid_type A (Var (x,A)) l
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B} l, rml_valid_type A (Const B c) l
| valid_let : forall A B x a b l {gz : n > 0}, rml_valid_type B a l -> rml_valid_type A b ((x,B) :: l) -> rml_valid_type A (@Let_stm n gz (x,B) a b) l
| valid_if : forall (A : Type) b m1 m2 l, rml_valid_type bool b l -> rml_valid_type A m1 l -> rml_valid_type A m2 l -> rml_valid_type A (If_stm b m1 m2) l
| valid_app : forall (A B : Type) e1 e2 l, rml_valid_type (B -> A) e1 l -> rml_valid_type B e2 l -> rml_valid_type A (App_stm B e1 e2) l.
                                                                                            
(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall {n : nat} x A l `{x_valid : rml_valid_type A x l},
    @well_formed n l x.
Proof.
  induction x ; intros.
  - destruct p.
    apply well_var.
    inversion x_valid ; subst.
    assumption.
  - apply well_const.
  - inversion x_valid ; subst.
    apply well_let_stm.
    + apply (IHx1 B).
      assumption.
    + apply (IHx2 A ((x,B) :: l)).
      assumption.      
  - inversion x_valid ; subst.
    apply well_if.
    + apply (IHx1 bool).
      assumption.
    + apply (IHx2 A).
      assumption.
    + apply (IHx3 A).
      assumption.
  - inversion x_valid ; subst.
    apply well_app.
    + apply (IHx1 (T -> A)).
      assumption.
    + apply (IHx2 T).
      assumption.
Defined.

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple {n : nat} : @Rml n -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml {n : nat} {A : Type} (rml : @Rml n) `{rml_simple : rml_is_simple rml} `{rml_valid : rml_valid_type A rml nil} : @sRml A.
Proof.
  (* apply is_rml_simple_reflect_rml_is_simple in rml_simple. *)
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (forall (A B : Type) c l, @rml_valid_type n A (Const B c) l -> A = B) by (intros ; inversion H ; subst ; reflexivity).
    assert (A = A0) by (apply (H A A0 a nil) ; assumption).
    subst.
    refine (sConst a).
  - exfalso.
    easy.
  - assert (if_valid_type : (rml_valid_type bool r1 nil /\ rml_valid_type A r2 nil /\ rml_valid_type A r3 nil)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.
    
    refine (sIf_stm (@rml_to_sRml n bool r1 s1 p1) (@rml_to_sRml n A r2 s2 p2) (@rml_to_sRml n A r3 s3 p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) r1 nil /\ rml_valid_type T r2 nil) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : rml_is_simple r1 /\ rml_is_simple r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    apply (sApp_stm T (@rml_to_sRml n (T -> A) r1 H1 p1) (@rml_to_sRml n T r2 H2 p2)).
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_for_let_simple_helper :
  forall n x A l `{x_valid : rml_valid_type A x (map fst l)} `{x_well : well_formed (map fst l) x},
    (forall k, List.In k l -> rml_is_simple k.2) ->
    rml_is_simple
      (@replace_all_variables_aux n x l x_well).
Proof.
  induction x ; intros.
  - induction l.
    + inversion x_valid ; subst.
      contradiction.
    + simpl.
      destruct pselect.
      * simpl.
        apply H.
        simpl.
        left.
        reflexivity.
      * simpl.
(*         apply IHl. *)
(*         -- inversion x_valid ; subst. *)
(*            inversion H2. *)
(*            ++ contradiction. *)
(*            ++ constructor. *)
(*               assumption. *)
(*         -- intros. *)
(*            apply H. *)
(*            simpl. *)
(*            right. *)
(*            assumption. *)
(*   - simpl. *)
(*     constructor. *)
(*   - simpl. *)
(*     apply IHx2 with (A := A). *)
(*     + simpl. *)
(*       inversion x_valid ; subst. *)
(*       assumption. *)
(*     + intros. *)
(*       inversion H0 ; subst. *)
(*       * simpl. *)
(*         inversion x_valid ; subst. *)
(*         apply IHx1 with (A := B). *)
(*         -- assumption. *)
(*         -- assumption. *)
(*       * apply H. *)
(*         assumption. *)
(*   - simpl. *)
(*     inversion x_valid ; subst. *)
(*     apply is_if ; eauto 2. *)
(*   - simpl. *)
(*     inversion x_valid ; subst. *)
(*     apply is_app ; eauto 2.   *)
(* Qed. *)
Admitted.
        
Theorem replace_var_for_let_simple :
  forall n (x : @Rml n) {A} `{x_valid : rml_valid_type A x nil},
  rml_is_simple (@replace_all_variables n x (@valid_is_well n x A nil x_valid)).
Proof.
  unfold replace_all_variables.
  intros.
  apply replace_var_for_let_simple_helper with (A := A).
  - simpl.
    assumption.
  - intros.
    contradiction.
Qed.

Theorem replace_var_for_let_valid_helper :
  forall n x A l `{x_valid : rml_valid_type A x (map fst l)},
    (forall p, List.In p (map fst l) -> rml_valid_type p.2 (lookup l p) (map fst l)) ->
    rml_valid_type A (@replace_all_variables_aux n x l (@valid_is_well n x A (map fst l) x_valid)) (map fst l).
Proof.
  induction x ; intros.
  - inversion x_valid ; subst.
    simpl.
    induction l.
    + contradiction.
    + destruct a.
      destruct p.
      apply (H (x,A)).
      * assumption.
  - simpl.
    constructor.
    inversion x_valid ; subst.
    reflexivity.
  - simpl.
    inversion x_valid ; subst.
    induction n.
    + inversion i.
    + 
    
Admitted.

Theorem replace_var_for_let_valid :
  forall n (x : Rml) {A} `{x_valid : rml_valid_type A x nil},
    rml_valid_type A (@replace_all_variables_aux n x nil) nil.
Proof.
  intros.
  apply replace_var_for_let_valid_helper.
  - assumption.
  - contradiction.
Qed.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {n : nat} {R} (x : @Rml n) {A} `{x_valid : rml_valid_type A x nil} : continuation_monad_type R A :=
  let y := @replace_all_variables n x (@valid_is_well n x A nil x_valid) in
  let y_simple := @replace_var_for_let_simple n x A x_valid in
  let y_valid := @replace_var_for_let_valid n x A x_valid in
  (interp_srml (@rml_to_sRml 0 A y y_simple y_valid)).