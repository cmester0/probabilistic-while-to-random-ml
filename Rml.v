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
| Let_stm : forall {_ : n > 0}, (nat * Type) -> @Rml n.+1 -> @Rml n.+1 -> Rml
(* | Fun_stm : forall B, (nat * Type) -> B -> Rml -> Rml *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed {n : nat} : seq (nat * Type) -> @Rml n -> Prop :=
| well_var : forall A x l, List.In (x,A) l -> well_formed l (Var (x,A))
| well_const : forall A c l, well_formed l (Const A c)
| well_let_stm : forall x (e1 e2 : @Rml n.+1) l {nz : n > 0}, @well_formed n.+1 l e1 -> @well_formed n.+1 (x :: l) e2 -> well_formed l (@Let_stm n nz x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type {n : nat} : Type -> @Rml n -> seq (nat * Type) -> Prop :=
| valid_var : forall x l A,
    List.In (x,A) l ->
    rml_valid_type A (Var (x,A)) l
                   
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B} l,
    rml_valid_type A (Const B c) l
                   
| valid_let : forall A B x a b l {nz : n > 0},
    @rml_valid_type n.+1 B a l ->
    @rml_valid_type n.+1 A b ((x,B) :: l) ->
    rml_valid_type A (@Let_stm n nz (x,B) a b) l
                   
| valid_if : forall (A : Type) b m1 m2 l,
    rml_valid_type bool b l ->
    rml_valid_type A m1 l ->
    rml_valid_type A m2 l ->
    rml_valid_type A (If_stm b m1 m2) l
                   
| valid_app : forall (A B : Type) e1 e2 l,
    rml_valid_type (B -> A) e1 l ->
    rml_valid_type B e2 l ->
    rml_valid_type A (App_stm B e1 e2) l.

(* -------------------------------------------------------------------------------- *)

Fixpoint lookup (env : seq (nat * Type * @Rml 0)) (p : (nat * Type)) :
  List.In p (map fst env) -> @Rml 0.
  intros.  
  induction env.
  - contradiction.
  - destruct (pselect (a.1 = p)).
    + intros.
      refine a.2.
    + intros.
      apply (lookup env p).
      inversion H.
      * contradiction.
      * assumption.
Defined.

Lemma valid_empty_env :
  forall (n : nat) (A : Type) (t : List.In (n, A) nil), rml_valid_type A (lookup nil (n, A) t) nil.
Proof. contradiction. Defined.

Fixpoint replace_all_variables_aux_type {n : nat} A (x : @Rml n) (env : seq (nat * Type * @Rml 0)) `{x_valid : @rml_valid_type n A x (map fst env)} : @Rml 0.
Proof.
  generalize dependent env.
  generalize dependent A.
  induction x ; intros.
  - assert (List.In p (map fst env)) by (inversion x_valid ; subst ; easy).
    refine (lookup env p H).
  - assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (Const A a).
  - destruct p.
    assert (x1_valid : rml_valid_type T x1 (map fst env)) by (inversion x_valid ; subst ; assumption).

    pose (a' := IHx1 T env x1_valid).
    pose (env' := ((n0,T),a') :: env).
    
    assert (x2_valid : rml_valid_type A x2 ((map fst env'))) by (inversion x_valid ; subst ; assumption).
    
    refine (replace_all_variables_aux_type n.+1 A x2 (((n0,T),a') :: env) x2_valid).
  - assert (x1_valid : rml_valid_type bool x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A x3 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type n bool x1 env x1_valid).
    pose (m1' := replace_all_variables_aux_type n A x2 env x2_valid).
    pose (m2' := replace_all_variables_aux_type n A x3 env x3_valid).

    refine (If_stm b' m1' m2').
  - assert (x1_valid : rml_valid_type (T -> A) x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type T x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type n (T -> A) x1 env x1_valid).
    pose (e2' := replace_all_variables_aux_type n T x2 env x2_valid).

    refine (App_stm T e1' e2').
Defined.

(* Fixpoint replace_all_variables_aux (x : Rml) (env : seq (nat * Type * Rml)) `{valid_env : forall n A (t : List.In (n,A) (map fst env)), rml_valid_type A (lookup env (n,A) t) (map fst env)} `{x_well : well_formed (map fst env) x} : Rml. *)
(* Proof. *)
(*   induction x. *)
(*   - apply (lookup env p). *)
(*     (* * apply valid_env. *) *)
(*     * inversion x_well ; subst. *)
(*       assumption. *)
(*   - refine (Const A a). *)
(*   - assert (a_well : well_formed [seq i.1 | i <- env] x1) by (inversion x_well ; eauto). *)
(*     pose (a := IHx1 a_well). *)
(*     pose (a' := replace_all_variables_aux x1 env valid_env a_well). *)
(*     pose (replace_all_variables_aux x2 ((p,a') :: env)). *)
(*     apply r. *)
(*     + inversion x_well ; subst. *)
(*       apply add_to_env. *)
      
(*       assumption. *)
(*     + *)
(*   - assert (b_well : well_formed [seq i.1 | i <- env] x1) by (inversion x_well ; eauto). *)
(*     assert (m1_well : well_formed [seq i.1 | i <- env] x2) by (inversion x_well ; eauto). *)
(*     assert (m2_well : well_formed [seq i.1 | i <- env] x3) by (inversion x_well ; eauto). *)
(*     pose (b := IHx1 b_well). *)
(*     pose (m1 := IHx2 m1_well). *)
(*     pose (m2 := IHx3 m2_well). *)
(*     refine (If_stm b m1 m2). *)
(*   - assert (e1_well : well_formed [seq i.1 | i <- env] x1) by (inversion x_well ; eauto). *)
(*     assert (e2_well : well_formed [seq i.1 | i <- env] x2) by (inversion x_well ; eauto). *)
(*     pose (e1 := IHx1 e1_well). *)
(*     pose (e2 := IHx2 e2_well). *)
(*     refine (App_stm T e1 e2). *)
(* Defined. *)
    
(* Fixpoint replace_all_variables_aux (x : Rml) (env : seq (nat * Type * Rml)) : Rml := *)
(*   match x with *)
(*   | Var n => lookup env n *)
(*   | Const _ _ => x *)
(*   | Let_stm n a b => *)
(*     let a' := replace_all_variables_aux a env in *)
(*     replace_all_variables_aux b ((n,a') :: env) *)
(*   | If_stm b m1 m2 => *)
(*     let b' := replace_all_variables_aux b env in *)
(*     let m1' := replace_all_variables_aux m1 env in *)
(*     let m2' := replace_all_variables_aux m2 env in *)
(*     If_stm b' m1' m2' *)
(*   | App_stm T e1 e2 => *)
(*     let e1' := replace_all_variables_aux e1 env in *)
(*     let e2' := replace_all_variables_aux e2 env in *)
(*     App_stm T e1' e2' *)
(*   end. *)

(* Definition replace_all_variables (x : Rml) `{x_well : well_formed nil x} : Rml := *)
(*   @replace_all_variables_aux x nil x_well. *)

Definition replace_all_variables_type {n : nat} A (x : @Rml n) `{x_valid : rml_valid_type A x nil} :=
  @replace_all_variables_aux_type n A x nil x_valid.

(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall {n} (x : @Rml n) A l `{x_valid : rml_valid_type A x l},
    well_formed l x.
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

Inductive rml_is_simple {n : nat} : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (@Const n A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (@If_stm n b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (@App_stm n B e1 e2).

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml {n : nat} {A : Type} (rml : @Rml n) `{rml_simple : @rml_is_simple n rml} `{rml_valid : @rml_valid_type n A rml nil} : @sRml A.
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
  forall n (x : @Rml n) A l `{x_valid : rml_valid_type A x (map fst l)},
    (forall k, List.In k l -> rml_is_simple k.2) ->
    rml_is_simple
      (@replace_all_variables_aux_type n A x l x_valid).
Proof.  
(*   induction x ; intros. *)
(*   - induction l. *)
(*     + inversion x_valid ; subst. *)
(*       contradiction.   *)
(*     + simpl. *)
(*       destruct pselect. *)
(*       * simpl. *)
(*         apply H. *)
(*         simpl. *)
(*         left. *)
(*         reflexivity. *)
(*       * simpl. *)
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
(*     apply is_app ; eauto 2. *)
(* Defined. *)
Admitted.

Theorem replace_var_for_let_simple :
  forall n (x : @Rml n) {A} `{x_valid : rml_valid_type A x nil},
  rml_is_simple (@replace_all_variables_type n A x x_valid).
Proof.
  intros.
  apply replace_var_for_let_simple_helper.
  contradiction.
Defined.
  
(*   apply replace_var_for_let_simple_helper with (A := A). *)
(*   - simpl. *)
(*     assumption. *)
(*   - intros. *)
(*     contradiction. *)
(* Defined. *)

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_for_let_valid_helper_var :
  forall n A p l `{x_valid : rml_valid_type A (Var p) (map fst l)} `{env_valid : forall (n : nat) (A : Type) (t : List.In (n, A) [seq i.1 | i <- l]), rml_valid_type A (lookup l (n, A) t) nil},
    rml_valid_type A (@replace_all_variables_aux_type n A (Var p) l x_valid) nil.
Proof.
  intros.
  destruct p.
  inversion x_valid ; subst.
  apply env_valid.
Defined.

Theorem replace_var_for_let_valid_helper_const :
  forall n A B c l `{x_valid : rml_valid_type A (Const B c) (map fst l)},
    rml_valid_type A (@replace_all_variables_aux_type n A (Const B c) l x_valid) nil.
Proof.
  induction n.
  intros.
  simpl.
  inversion x_valid ; subst.
  simpl replace_all_variables_aux_type.
  reflexivity.
Defined.

Theorem replace_var_for_let_valid_helper :
  forall x A l `{x_valid : rml_valid_type A x (map fst l)}
      `{env_valid :
        forall (n : nat) (A : Type) (t : List.In (n, A) [seq i.1 | i <- l]),
          rml_valid_type A (lookup l (n, A) t) nil},
    rml_valid_type A (@replace_all_variables_aux_type A x l env_valid x_valid) nil.
Proof.
  induction x ; intros.
  - apply replace_var_for_let_valid_helper_var ; assumption.
  - apply replace_var_for_let_valid_helper_const ; assumption.
  - simpl.
    inversion x_valid ; subst.
    simpl.
    apply IHx2.
  - simpl.
    inversion x_valid.
    constructor ; eauto.
  - simpl.
    inversion x_valid.
    constructor ; eauto.
Defined.

Theorem replace_var_for_let_valid :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x nil},
    rml_valid_type A (@replace_all_variables_aux_type A x nil valid_empty_env x_valid) nil.
Proof.
  intros.
  apply replace_var_for_let_valid_helper.
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x nil} : continuation_monad_type R A :=
  let y := @replace_all_variables_type A x x_valid in
  let y_simple := @replace_var_for_let_simple x A x_valid in
  let y_valid := @replace_var_for_let_valid x A x_valid in
  (interp_srml (@rml_to_sRml A y y_simple y_valid)).