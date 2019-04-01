From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.reals.
From mathcomp.analysis Require Import boolp reals distr.

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

Inductive Rml : Type :=
| Var : (nat * Type) -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : (nat * Type) -> @Rml -> @Rml -> Rml
(* | Fun_stm : forall B, (nat * Type) -> B -> Rml -> Rml *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed : seq (nat * Type) -> Rml -> Prop :=
| well_var : forall A x l, List.In (x,A) l -> well_formed l (Var (x,A))
| well_const : forall A c l, well_formed l (Const A c)
| well_let_stm : forall x (e1 e2 : Rml) l, @well_formed l e1 -> @well_formed (x :: l) e2 -> well_formed l (Let_stm x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type : Type -> Rml -> seq (nat * Type) -> Prop :=
| valid_var : forall x l A,
    List.In (x,A) l ->
    rml_valid_type A (Var (x,A)) l
                   
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B} l,
    rml_valid_type A (Const B c) l
                   
| valid_let : forall A B x a b l,
    @rml_valid_type B a l ->
    @rml_valid_type A b ((x,B) :: l) ->
    rml_valid_type A (Let_stm (x,B) a b) l
                   
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

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (@Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (@If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (@App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml {A : Type} (rml : Rml) `{rml_simple : @rml_is_simple rml} `{rml_valid : @rml_valid_type A rml nil} : @sRml A.
Proof.
  (* apply is_rml_simple_reflect_rml_is_simple in rml_simple. *)
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (forall (A B : Type) c l, @rml_valid_type A (Const B c) l -> A = B) by (intros ; inversion H ; subst ; reflexivity).
    assert (A = A0) by (apply (H A A0 a nil) ; assumption).
    subst.
    refine (sConst a).
  - exfalso.
    easy.
  - assert (if_valid_type : (rml_valid_type bool r1 nil /\ rml_valid_type A r2 nil /\ rml_valid_type A r3 nil)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.
    
    refine (sIf_stm (@rml_to_sRml bool r1 s1 p1) (@rml_to_sRml A r2 s2 p2) (@rml_to_sRml A r3 s3 p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) r1 nil /\ rml_valid_type T r2 nil) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : rml_is_simple r1 /\ rml_is_simple r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    apply (sApp_stm T (@rml_to_sRml (T -> A) r1 H1 p1) (@rml_to_sRml T r2 H2 p2)).
Defined.

(** Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * Type * Rml) -> Prop :=
| env_nil : valid_env nil
| env_cons (x : nat * Type * Rml) xs :
    (rml_is_simple x.2) ->
    (rml_valid_type x.1.2 x.2 nil) ->
    valid_env xs ->
    valid_env (x :: xs).

Lemma valid_env_valid {l} (env_valid : valid_env l) :
  forall k, List.In k l -> rml_valid_type k.1.2 k.2 nil.
Proof.
  intros.
  induction l.
  - contradiction.
  - inversion env_valid ; subst.
    inversion H ; subst.
    + assumption.
    + apply IHl ; assumption.
Qed.

Lemma valid_env_simple {l} (env_valid : valid_env l) :
  forall k, List.In k l -> rml_is_simple k.2.
Proof.
  intros.
  induction l.
  - contradiction.
  - inversion env_valid ; subst.
    inversion H ; subst.
    + assumption.
    + apply IHl ; assumption.
Qed.

Fixpoint lookup (p : (nat * Type)) (env : seq (nat * Type * Rml)) `{env_valid : valid_env env} :
  List.In p (map fst env) -> Rml.
  intros.
  induction env.
  - contradiction.
  - destruct (pselect (a.1 = p)).
    + intros.
      refine a.2.
    + intros.
      apply IHenv.
      * inversion env_valid ; subst ; assumption.
      * inversion H ; subst ; easy.
Defined.

Lemma in_pair_list :
  forall {A B k l}, @List.In (A * B) k l -> @List.In A k.1 (map fst l).
Proof.
  intros.
  induction l.
  - contradiction.
  - simpl in H.
    inversion H ; subst.
    + left. reflexivity.
    + right.
      apply IHl.
      assumption.
Qed.

Lemma valid_weakening :
  forall x T l1 l2 l3,
    rml_valid_type T x (l3 ++ l1) -> rml_valid_type T x (l3 ++ l2 ++ l1).
Proof.
  induction x ; intros.
  - inversion H ; subst.
    apply List.in_app_or in H2.
    constructor.
    apply List.in_or_app.
    inversion H2 ; subst.
    + left. assumption.
    + right.
      apply List.in_or_app.
      right.
      assumption.
  - inversion H ; subst.
    constructor ; reflexivity.
  - inversion H ; subst.
    constructor.
    apply IHx1 ; assumption.
    apply (IHx2 T l1 l2 ((x,B) :: l3)) ; assumption.
  - inversion H ; subst.
    constructor ; eauto 2.
  - inversion H ; subst.
    constructor ; eauto 2.
Qed.

Corollary valid_weakening_rm :
  forall x T l1 l2,
    rml_valid_type T x l1 -> rml_valid_type T x (l2 ++ l1).
Proof.
  intros.
  apply (valid_weakening x T l1 l2 nil).
  assumption.
Qed.

Corollary valid_weakening_empty :
  forall x T l,
    rml_valid_type T x nil -> rml_valid_type T x l.
Proof.
  intros.
  rewrite <- List.app_nil_r.
  apply (valid_weakening x T nil l nil).
  assumption.
Qed.

Lemma valid_env_weakening :
  forall T l a p env `{env_valid : valid_env env} `{pl : List.In p env} `{a_env_valid : valid_env (a :: env)} `{a_pl : List.In p (a :: env)},
    p.1.2 = T ->
    rml_valid_type T (@lookup p.1 env env_valid (in_pair_list pl)) l ->
    rml_valid_type T (@lookup p.1 (a :: env) a_env_valid (in_pair_list a_pl)) l.
Proof.
  intros.
  destruct p.
  destruct p.
  destruct a.
  destruct p.
  simpl.
  destruct pselect.
  - subst.
    inversion a_env_valid ; subst.
    simpl fst in *.
    simpl snd in *.
    inversion e ; subst.
    apply valid_weakening_empty.
    assumption.
  -
Admitted.
    
Lemma lookup_valid :
  forall env `{env_valid : valid_env env},
  forall k (ki : List.In k env),
    rml_valid_type k.1.2 (@lookup k.1 env env_valid (in_pair_list ki)) nil.
Proof.
  induction env.
  - contradiction.
  - inversion env_valid ; subst.
    destruct k.
    destruct p.
    intros.
    inversion ki.
    + destruct a.
      destruct p.
      inversion H ; subst.
      apply valid_weakening_empty.
      simpl in *.
      destruct pselect ; try contradiction.
      simpl.
      assumption.
    + pose (IHenv H3 (n,T,r) H).
      destruct a.
      destruct p.
      simpl fst in *.
      simpl snd in *.

      fold (map fst env).
      
      pose (@valid_env_weakening T nil (n0,T0,r1) (n,T,r) env H3 H env_valid ki).
      apply r2.
      reflexivity.
      assumption.
Qed.      

Lemma lookup_simple :
  forall env `{env_valid : valid_env env},
  forall p (pi : List.In p (map fst env)),
    rml_is_simple (@lookup p env env_valid pi).
Proof.
  intros.
  destruct p.
  induction env.
  - contradiction.
  - simpl.
    destruct pselect.
    + inversion env_valid ; subst.
      assumption.
    + inversion pi.
      * destruct a.
        simpl fst in *.
        inversion H ; subst.
        contradiction.
      * inversion env_valid ; subst.
        (* apply (IHenv H4 H). *)
Admitted.  

Lemma inside :
  forall env `{env_valid : valid_env env},
  forall p (pi : List.In p (map fst env)), List.In (p,@lookup p env env_valid pi) env.
Proof.
Admitted.

(* Lemma valid_empty_env : *)
(*   forall (n : nat) (A : Type) (t : List.In (n, A) nil), *)
(*     rml_valid_type A (@lookup nil env_nil (n, A) t) nil. *)
(* Proof. contradiction. Defined. *)

Fixpoint replace_all_variables_aux_type A (x : Rml) (env : seq (nat * Type * Rml))
         `{env_valid : valid_env env} `{x_valid : @rml_valid_type A x (map fst env)} : @sRml A.
Proof.
  generalize dependent env.
  generalize dependent A.
  induction x ; intros.
  - assert (List.In p (map fst env)) by (inversion x_valid ; subst ; easy).

    destruct p.
    
    pose (@inside env env_valid (n,T) H).
    pose (r_valid := @lookup_valid env env_valid ((n,T),@lookup (n,T) env env_valid H) i).
    simpl in *.
    pose (r := @lookup (n,T) env env_valid (in_pair_list i)).
    pose (r_simple := @lookup_simple env env_valid (n,T) (in_pair_list i)).
    pose (@rml_to_sRml T r r_simple r_valid).

    assert (A = T) by (inversion x_valid ; subst ; reflexivity) ; subst.
    apply s.
  - assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (sConst a).
  - destruct p.
    assert (x1_valid : rml_valid_type T x1 (map fst env)) by (inversion x_valid ; subst ; assumption).

    pose (a' := IHx1 T env env_valid x1_valid).
    
    assert (env_valid' : valid_env ((n,T,x1) :: env)).
    constructor.
    induction env.
    simpl in *.
    simpl.
    
    2 : assumption.
    
    
    assert (x2_valid : rml_valid_type A x2 (map fst ((n,T,a') :: env))) by (inversion x_valid ; subst ; assumption).      
    
    refine (replace_all_variables_aux_type A x2 ((n,T,a') :: env) env_valid x2_valid).
  - assert (x1_valid : rml_valid_type bool x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A x3 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type bool x1 env x1_valid).
    pose (m1' := replace_all_variables_aux_type A x2 env x2_valid).
    pose (m2' := replace_all_variables_aux_type A x3 env x3_valid).

    refine (If_stm b' m1' m2').
  - assert (x1_valid : rml_valid_type (T -> A) x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type T x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type (T -> A) x1 env x1_valid).
    pose (e2' := replace_all_variables_aux_type T x2 env x2_valid).

    refine (App_stm T e1' e2').
Defined.


Fixpoint replace_all_variables_aux_type A (x : Rml) (env : seq (nat * Type * Rml))
         `{env_valid : valid_env env} `{x_valid : @rml_valid_type A x (map fst env)} : Rml.
Proof.
  generalize dependent env.
  generalize dependent A.
  induction x ; intros.
  - assert (List.In p (map fst env)) by (inversion x_valid ; subst ; easy).
    refine (lookup env p H).
    assumption.
  - refine (Const A a).
    (* assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst. *)
    (* refine (Const A a). *)
  - destruct p.
    assert (x1_valid : rml_valid_type T x1 (map fst env)) by (inversion x_valid ; subst ; assumption).

    pose (a' := IHx1 T env env_valid x1_valid).
    
    assert (env_valid' : valid_env ((n,T,a') :: env)).
    constructor.
    induction env.
    simpl in *.
    simpl.
    2 : assumption.
    
    
    assert (x2_valid : rml_valid_type A x2 (map fst ((n,T,a') :: env))) by (inversion x_valid ; subst ; assumption).      
    
    refine (replace_all_variables_aux_type A x2 ((n,T,a') :: env) env_valid x2_valid).
  - assert (x1_valid : rml_valid_type bool x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A x3 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type bool x1 env x1_valid).
    pose (m1' := replace_all_variables_aux_type A x2 env x2_valid).
    pose (m2' := replace_all_variables_aux_type A x3 env x3_valid).

    refine (If_stm b' m1' m2').
  - assert (x1_valid : rml_valid_type (T -> A) x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type T x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type (T -> A) x1 env x1_valid).
    pose (e2' := replace_all_variables_aux_type T x2 env x2_valid).

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

Definition replace_all_variables_type A (x : Rml) `{x_valid : rml_valid_type A x nil} :=
  @replace_all_variables_aux_type A x nil x_valid.

(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall (x : Rml) A l `{x_valid : rml_valid_type A x l},
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

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_for_let_simple_helper :
  forall (x : Rml) A l `{x_valid : rml_valid_type A x (map fst l)},
    (forall k, List.In k l -> rml_is_simple k.2) ->
    rml_is_simple
      (@replace_all_variables_aux_type A x l x_valid).
Proof.
  induction x ; intros.
  - simpl.
  
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
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x nil},
  rml_is_simple (@replace_all_variables_type A x x_valid).
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
  forall A p l `{x_valid : rml_valid_type A (Var p) (map fst l)} `{env_valid : forall (n : nat) (A : Type) (t : List.In (n, A) [seq i.1 | i <- l]), rml_valid_type A (lookup l (n, A) t) nil},
    rml_valid_type A (@replace_all_variables_aux_type A (Var p) l x_valid) nil.
Proof.
  intros.
  destruct p.
  inversion x_valid ; subst.
  apply env_valid.
Defined.

Theorem replace_var_for_let_valid_helper_const :
  forall A B c l `{x_valid : rml_valid_type A (Const B c) (map fst l)},
    rml_valid_type A (@replace_all_variables_aux_type A (Const B c) l x_valid) nil.
Proof.
  intros.
  simpl in *.
  inversion x_valid ; subst.
  simpl.
  constructor.
  reflexivity.
Defined.

Theorem replace_var_for_let_valid_helper :
  forall x A l `{x_valid : rml_valid_type A x (map fst l)} `{env_valid : forall (n : nat) (A : Type) (t : List.In (n, A) [seq i.1 | i <- l]), rml_valid_type A (lookup l (n, A) t) nil},
    rml_valid_type A (@replace_all_variables_aux_type A x l x_valid) nil.
Proof.
  induction x ; intros.
  - apply replace_var_for_let_valid_helper_var ; assumption.
  - apply replace_var_for_let_valid_helper_const ; assumption.
  2: {
    simpl.
    inversion x_valid.
    constructor ; eauto.
  }
  2: {
    simpl.
    inversion x_valid.
    constructor ; eauto.
  }
  - simpl.

    inversion x_valid ; subst.
    (* apply IHx2 *)
Admitted.

Theorem replace_var_for_let_valid :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x nil},
    rml_valid_type A (@replace_all_variables_aux_type A x nil x_valid) nil.
Proof.
  intros.
  apply replace_var_for_let_valid_helper.
  apply valid_empty_env.
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x nil} : continuation_monad_type R A :=
  let y := @replace_all_variables_type A x x_valid in
  let y_simple := @replace_var_for_let_simple x A x_valid in
  let y_valid := @replace_var_for_let_valid x A x_valid in
  (interp_srml (@rml_to_sRml A y y_simple y_valid)).