From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.

(* -------------------------------------------------------------------------------- *)

Inductive Rml :=
| Var : (nat * Type) -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : (nat * Type) -> Rml -> Rml -> Rml
| Fun_stm : (nat * Type) -> Rml -> Rml
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml
| Let_rec : (nat * Type) -> (nat * Type) -> @Rml -> @Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed : seq (nat * Type) -> Rml -> Prop :=
| well_var : forall A x l,
    List.In (x,A) l ->
    well_formed l (Var (x,A))
                
| well_const : forall A c l,
    well_formed l (Const A c)
                
| well_let : forall x (e1 e2 : Rml) l,
    @well_formed l e1 ->
    @well_formed (x :: l) e2 ->
    well_formed l (Let_stm x e1 e2)

| well_fun : forall p x l,
    @well_formed (p :: l) x ->
    @well_formed l (Fun_stm p x)
                
| well_if : forall b m1 m2 l,
    well_formed l b ->
    well_formed l m1 ->
    well_formed l m2 ->
    well_formed l (If_stm b m1 m2)

| well_app : forall B e1 e2 l,
    well_formed l e1 ->
    well_formed l e2 ->
    well_formed l (App_stm B e1 e2)

| well_let_rec : forall f x (e1 e2 : Rml) l,
    @well_formed (x :: f :: l) e1 ->
    @well_formed (f :: l) e2 ->
    well_formed l (Let_rec f x e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} :=
| sVar : (nat * Type) -> sRml
| sConst : A -> sRml
| sFun : (nat * Type) -> sRml -> sRml
| sIf : @sRml bool -> sRml -> sRml -> sRml
| sApp : forall T, @sRml (T -> A) -> @sRml T -> sRml.
(* | sFix : forall (B : Type) (C : Type), @sRml ((B -> C) -> B -> C) -> @sRml (((B -> C) -> B -> C) -> A) -> sRml. *)

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type (A : Type) (l : seq (nat * Type)) : Rml -> Prop :=
| valid_var : forall x,
    List.In (x,A) l ->
    rml_valid_type A l (Var (x,A))
                   
| valid_const : forall (c : A),
    rml_valid_type A l (Const A c)
                   
| valid_let : forall B x a b,
    @rml_valid_type B l a ->
    @rml_valid_type A ((x,B) :: l) b ->
    rml_valid_type A l (Let_stm (x,B) a b)

| valid_fun : forall p x,
    rml_valid_type A (p :: l) x ->
    rml_valid_type A l (Fun_stm p x)
                   
| valid_if : forall b m1 m2,
    rml_valid_type bool l b ->
    rml_valid_type A l m1 ->
    rml_valid_type A l m2 ->
    rml_valid_type A l (If_stm b m1 m2)
                   
| valid_app : forall (B : Type) e1 e2,
    rml_valid_type (B -> A) l e1 ->
    rml_valid_type B l e2 ->
    rml_valid_type A l (App_stm B e1 e2)

| valid_let_rec : forall B C f x a b,
    @rml_valid_type (B -> C) ((x,B) :: (f,B -> C) :: l) a ->
    @rml_valid_type A ((f,B -> C) :: l) b ->
    rml_valid_type A l (Let_rec (f,B -> C) (x,B) a b).

(* -------------------------------------------------------------------------------- *)

Definition p_in_list (p : nat*Type) (l : seq (nat * Type)) : bool.
Proof.
  induction l.
  - refine false.
  - refine (if (pselect (a = p))
            then true
            else IHl).  
Defined.

Theorem in_list_func :
  forall p l,
    p_in_list p l -> List.In p l.
Proof.
  intros.
  induction l.
  - inversion H. (* false *)
  - simpl in H.
    destruct pselect.
    left.
    assumption.
    right.
    apply IHl.
    simpl in H.
    assumption.
Defined.

Definition ob :=
  fun {A B} (x : option A) (f : A -> option B) =>
    match x with
    | Some y => f y
    | None => None
    end.

Fixpoint compute_valid A l (x : Rml) : option (rml_valid_type A l x).
Proof.
  generalize dependent A.
  generalize dependent l.
  induction x ; intros.
  - destruct (p_in_list p l) eqn : opil.
    + apply in_list_func in opil.
      destruct p.
      pose (Some (valid_var T l n opil)).
      destruct (pselect (A = T)).
      * subst.
        assumption.
      * refine None.
    + refine None.
  - case (pselect (A0 = A)) ; intros.
    + subst.
      refine (Some (valid_const A l a)).
    + refine None.
  - destruct p.
    pose (ob (IHx1 l T) (fun valid_x1 =>
          ob (IHx2 ((n,T) :: l) A) (fun valid_x2 =>
          Some (valid_let A l T n x1 x2 valid_x1 valid_x2)))).
    apply o.
  - apply (ob (IHx (p :: l) A) (fun valid_x => Some (valid_fun A l p x valid_x))).
  - apply (ob (IHx1 l bool) (fun valid_x1 =>
          ob (IHx2 l A) (fun valid_x2 =>
          ob (IHx3 l A) (fun valid_x3 =>
          Some (valid_if A l x1 x2 x3 valid_x1 valid_x2 valid_x3))))).
  - apply (ob (IHx1 l (T -> A)) (fun valid_x1 =>
          ob (IHx2 l T) (fun valid_x2 =>
          Some (valid_app A l T x1 x2 valid_x1 valid_x2)))).
  - apply None.
Defined.

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple {l : seq (nat * Type)} : Rml -> Prop :=
| is_var : forall (p : nat * Type), List.In p l -> rml_is_simple (Var p)
| is_const : forall (A : Type) c, rml_is_simple (@Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (@If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (@App_stm B e1 e2)
| is_fun : forall p x, @rml_is_simple (p :: l) x -> rml_is_simple (@Fun_stm p x).

(* -------------------------------------------------------------------------------- *)

Definition Y p1 p2 A B :=
  Fun_stm p1 (App_stm A
(Fun_stm p2 (App_stm B (Var p1) (App_stm B (Var p2) (Var p2))))
(Fun_stm p2 (App_stm B (Var p1) (App_stm B (Var p2) (Var p2))))).

Definition sY p1 p2 A B :=
  @sFun A p1 (sApp A
(sFun p2 (sApp B (sVar p1) (sApp B (sVar p2) (sVar p2))))
(sFun p2 (sApp B (sVar p1) (sApp B (sVar p2) (sVar p2))))).

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml_l {A : Type} (rml : Rml) l `{rml_simple : @rml_is_simple l rml} `{rml_valid : @rml_valid_type A l rml} : @sRml A.
Proof.
  case rml eqn : o_rml.
  - exact (sVar p).
  - assert (A0 = A) by (inversion rml_valid ; subst ; reflexivity) ; subst.
    exact (sConst a).
  - exfalso.
    easy.
  - assert (fun_valid_type : (rml_valid_type A (p :: l) r)) by (inversion rml_valid ; subst ; assumption).

    assert (@rml_is_simple [:: p & l] r) by (inversion rml_simple ; subst ; assumption).

    pose (rml_to_sRml_l A r (p :: l) H fun_valid_type).

    exact (sFun p s).
    
  - assert (if_valid_type : (rml_valid_type bool l r1 /\ rml_valid_type A l r2 /\ rml_valid_type A l r3)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : @rml_is_simple l r1 /\ @rml_is_simple l r2 /\ @rml_is_simple l r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.

    exact (sIf (@rml_to_sRml_l bool r1 l s1 p1) (@rml_to_sRml_l A r2 l s2 p2) (@rml_to_sRml_l A r3 l s3 p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) l r1 /\ rml_valid_type T l r2) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : @rml_is_simple l r1 /\ @rml_is_simple l r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    exact (sApp T (@rml_to_sRml_l (T -> A) r1 l H1 p1) (@rml_to_sRml_l T r2 l H2 p2)).
  - assert (@rml_is_simple [:: p0 , p & l] r1) by
        (inversion rml_simple ; assumption).
    assert (rml_valid_type p.2 [:: p0 , p & l] r1) by
        (inversion rml_valid ; assumption).
    pose (@rml_to_sRml_l p.2 r1 [:: p0, p & l] H H0).

    pose (sY p p0 A p0.2).
    exact s0.
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint sRml_to_rml {A} (x : @sRml A) : Rml :=
  match x with
  | sVar p => Var p
  | sConst c => Const A c
  | sFun p x => Fun_stm p (sRml_to_rml x)
  | sIf b m1 m2 => If_stm (sRml_to_rml b) (sRml_to_rml m1) (sRml_to_rml m2)
  | sApp T e1 e2 => App_stm T (sRml_to_rml e1) (sRml_to_rml e2)
  (* | sFix B C f k => App_stm ((B -> C) -> B -> C) (sRml_to_rml k) (sRml_to_rml f) *)
  end.

(* Lemma sRml_simple : *)
(*   forall A (x : Rml) `{x_simple : @rml_is_simple nil x}, *)
(*     forall y, compute_valid A nil x = Some y -> *)
(*     @rml_is_simple nil (@sRml_to_rml A (@rml_to_sRml_l A x nil x_simple y)). *)
(* Proof. *)
(*   intros. *)
(*   generalize dependent A. *)
(*   induction x ; intros. *)
(*   - inversion H. (* Contradiction *) *)
(*   - inversion H ; subst. *)
(*     destruct pselect. *)
(*     + unfold eq_rec_r in H1. *)
(*       unfold eq_rec in H1. *)
(*       unfold eq_rect in H1. *)
(*       unfold Logic.eq_sym in H1. *)
(*       destruct e. *)
(*       assert (valid_const A0 nil a = y) by (apply Some_inj in H1 ; assumption). *)
(*       subst. *)
(*       simpl. *)
(*       constructor. *)
(*     + inversion H1. *)
(*   - inversion x_simple. *)
(*   - simpl. *)
(*     constructor. *)
(*     inversion x_simple ; subst. *)
(*     inversion y ; subst. *)
    
(*     pose (IHx). *)
    
(*     simpl in H. *)
(*     unfold ob in H. *)
(*     unfold eq_rec_r in H. *)
(*     unfold eq_rec in H. *)
(*     unfold eq_rect in H. *)
(*     unfold Logic.eq_sym in H. *)
(*     inversion x_simple ; subst. *)
(*     unfold Rml_rect in H. *)
(*     unfold p_in_list in H. *)
(*     unfold list_rec in H. *)
(*     unfold list_rect in H. *)
(*     simpl in H. *)
(*     destruct p. *)
(* Admitted. *)

Inductive srml_valid_type (A : Type) (l : seq (nat * Type)) : @sRml A -> Prop :=
| svalid_var : forall x,
    List.In (x,A) l ->
    srml_valid_type A l (sVar (x,A))
                   
| svalid_const : forall (c : A),
    srml_valid_type A l (sConst c)

| svalid_fun : forall p x,
    srml_valid_type A (p :: l) x ->
    srml_valid_type A l (sFun p x)
                   
| svalid_if : forall b m1 m2,
    srml_valid_type bool l b ->
    srml_valid_type A l m1 ->
    srml_valid_type A l m2 ->
    srml_valid_type A l (sIf b m1 m2)
                   
| svalid_app : forall (B : Type) e1 e2,
    @srml_valid_type (B -> A) l e1 ->
    @srml_valid_type B l e2 ->
    @srml_valid_type A l (sApp B e1 e2).

Compute compute_valid nat nil (Const nat 4).
Compute @rml_to_sRml_l (nat -> nat) (Const (nat -> nat) id) nil (is_const (nat -> nat) id) (valid_const (nat -> nat) [::] id).

Lemma helper :
  forall T A x1 x2 l, srml_valid_type A l (sApp T x1 x2) -> srml_valid_type (T -> A) l x1 /\ srml_valid_type T l x2.
Admitted.

Lemma sRml_simple :
  forall A (x : @sRml A) l (x_valid : srml_valid_type A l x),
    @rml_is_simple l (@sRml_to_rml A x).
Proof.
  induction x ; intros.
  - inversion x_valid.
    constructor.
    assumption.
  - constructor.
  - simpl.
    constructor.
    apply IHx.
    inversion x_valid.
    assumption.
  - simpl.
    inversion x_valid.
    constructor.
    + apply IHx1.      
      assumption.
    + apply IHx2.
      assumption.
    + apply IHx3.
      assumption.
  - simpl.
    apply helper in x_valid.
    inversion x_valid.
    constructor.
    + apply IHx1.
      assumption.
    + apply IHx2.
      assumption.
Qed.

Lemma sRml_valid :
  forall A (x : @sRml A) l (x_valid : srml_valid_type A l x),
    rml_valid_type A l (@sRml_to_rml A x).
Proof.
  induction x ; intros.
  - inversion x_valid.
    constructor.
    assumption.
  - constructor.
  - simpl.
    constructor.
    apply IHx.
    inversion x_valid ; subst.
    assumption.
  - simpl.
    inversion x_valid.
    constructor ; eauto.
  - simpl.
    apply helper in x_valid.
    inversion x_valid.
    constructor ; eauto.
Qed.

(** Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * Type * Rml) -> Prop :=
| env_nil : valid_env nil
| env_cons (x : nat * Type * Rml) xs :
    (@rml_is_simple (map fst xs) x.2) ->
    (@rml_valid_type x.1.2 (map fst xs) x.2) ->
    valid_env xs ->
    valid_env (x :: xs).

Lemma valid_weakening:
  forall (a : nat * Type * Rml) l1 l2 l3, rml_valid_type a.1.2 (l1 ++ l3) a.2 -> rml_valid_type a.1.2 (l1 ++ l2 ++ l3) a.2.
Proof.
  intros.
  destruct a.
  destruct p.
  simpl in *.
  generalize dependent T.
  generalize dependent l1.
  induction r ; intros.
  - inversion H ; subst.
    constructor.
    apply List.in_app_or in H1.
    inversion H1.
    + apply List.in_or_app.
      left.
      assumption.
    + apply List.in_or_app.
      right.
      apply List.in_or_app.
      right.
      assumption.
    + inversion H ; subst.
      constructor.
    + inversion H ; subst.
      constructor.
      * apply IHr1.
        assumption.
      * apply (IHr2 ((x,B) :: l1)).
        assumption.
    + constructor.
      inversion H ; subst.
      apply (IHr (p :: l1)).
      assumption.
    + inversion H ; subst.
      constructor ; eauto.
    + inversion H ; subst.
      constructor ; eauto.
    + inversion H ; subst.
      constructor.
      * apply (IHr1 [:: (x,B), (f,B -> C) & l1]).
        assumption.
      * apply (IHr2 [:: (f,B -> C) & l1]).
        assumption.
Qed.

Corollary valid_weakening_nil :
  forall (a : nat * Type * Rml) l1 l2, rml_valid_type a.1.2 (l1) a.2 -> rml_valid_type a.1.2 (l1 ++ l2) a.2.
Proof.
  intros.  
  pose (valid_weakening a l1 l2 nil%SEQ).
  rewrite <- (cats0 (l1 ++ l2)).
  rewrite <- catA.
  apply r.
  rewrite cats0.
  assumption.
Qed.
  
Fixpoint lookup (p : (nat * Type)) (env : seq (nat * Type * Rml)) `{env_valid : valid_env env} `{_ : List.In p (map fst env)} {struct env} : @sRml p.2.
  intros.
  induction env.
  - contradiction.
  - destruct (pselect (a.1 = p)).
    + intros.
      refine (rml_to_sRml_l a.2 (map fst env)) ; inversion env_valid ; subst.
      assumption.      
    + assumption.      
      apply IHenv.
      * inversion env_valid ; subst ; assumption.
      * inversion H ; subst ; easy.
Defined.

Definition replace_all_variables_aux_type_var A p (env : seq (nat * Type * Rml))
         `{env_valid : valid_env env} `{x_valid : @rml_valid_type A (map fst env) (Var p)} : @sRml A.
Proof.
  assert (List.In p (map fst env)) by (inversion x_valid ; subst ; easy).
  destruct p.
  assert (A = T) by (inversion x_valid ; subst ; reflexivity) ; subst.
  refine (@lookup (n,T) env env_valid H).
Defined.

Definition replace_all_variables_aux_type_const A0 A a (env : seq (nat * Type * Rml))
         `{env_valid : valid_env env} `{x_valid : @rml_valid_type A0 (map fst env) (Const A a)} : @sRml A0.
Proof.
  assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
  refine (sConst a).
Defined.

Lemma valid_rml_makes_valid_srml :
  forall A x y l, rml_valid_type A l x -> srml_valid_type A l y.
Admitted.

Fixpoint replace_all_variables_aux_type A (x : Rml) (env : seq (nat * Type * Rml))
         `{env_valid : valid_env env} `{x_valid : @rml_valid_type A (map fst env) x} : @sRml A.
Proof.
  generalize dependent env.
  generalize dependent A.  
  induction x ; intros.
  - apply (@replace_all_variables_aux_type_var A p env env_valid x_valid).
  - apply (@replace_all_variables_aux_type_const A0 A a env env_valid x_valid).
  - destruct p.
    assert (x1_valid : rml_valid_type T [seq i.1 | i <- env] x1) by (inversion x_valid ; subst ; assumption).
    
    pose (x1' := IHx1 T env env_valid x1_valid).
    
    pose (x1'' := sRml_to_rml x1').

    pose (x1'_valid := valid_rml_makes_valid_srml T x1 x1' [seq i.1 | i <- env] x1_valid).

    Check @sRml_simple.
    
    pose (x1''_simple := @sRml_simple T x1' [seq i.1 | i <- env] x1'_valid).
    pose (x1''_valid := sRml_valid T x1' [seq i.1 | i <- env] x1'_valid).    

    assert (x2_valid : rml_valid_type A ((n,T) :: [seq i.1 | i <- env]) x2) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((n,T,x1'') :: env)) by (constructor ; assumption).
    
    refine (IHx2 A ((n,T,x1'') :: env) env_valid' x2_valid).
  - assert (fun_valid : rml_valid_type A (p :: (map fst env)) x) by (inversion x_valid ; subst ; assumption).

    assert (fun_env_valid : valid_env ((p,y) :: env)).
    constructor.
    + simpl.
      constructor.
    + simpl.
      destruct p.
      simpl.
      constructor.
    
    
    pose (x' := IHx A ((p,x) :: env) env_valid fun_valid).
    
    refine (sFun p x).
    

    refine (Let_stm p (Var p)).
    
    refine (rml_to_sRml_l (Fun_stm )).

    
  - assert (x1_valid : rml_valid_type bool (map fst env) x1) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A (map fst env) x2) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A (map fst env) x3) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type bool x1 env env_valid x1_valid).
    pose (m1' := replace_all_variables_aux_type A x2 env env_valid x2_valid).
    pose (m2' := replace_all_variables_aux_type A x3 env env_valid x3_valid).

    pose (b'' := sRml_to_rml b').
    pose (m1'' := sRml_to_rml m1').
    pose (m2'' := sRml_to_rml m2').
    
    refine (rml_to_sRml (If_stm b'' m1'' m2'')).
    constructor ; eauto using sRml_simple.
    constructor ; eauto using sRml_valid.
    
  - assert (x1_valid : rml_valid_type (T -> A) (map fst env) x1) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type T (map fst env) x2) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type (T -> A) x1 env env_valid x1_valid).
    pose (e2' := replace_all_variables_aux_type T x2 env env_valid x2_valid).

    pose (e1'' := sRml_to_rml e1').
    pose (e2'' := sRml_to_rml e2').

    refine (rml_to_sRml (App_stm T e1'' e2'')).
    constructor ; eauto using sRml_simple.
    constructor ; eauto using sRml_valid.

  - (* let_rec f x = e1 in e2 *)    
Admitted.

Definition replace_all_variables_type A (x : Rml) `{x_valid : rml_valid_type A nil x} :=
  @replace_all_variables_aux_type A x nil env_nil x_valid.

(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall (x : Rml) A l `{x_valid : rml_valid_type A l x},
    well_formed l x.
Proof.
  induction x ; intros ; inversion x_valid ; subst ; try (constructor ; eauto).
Qed.

(* -------------------------------------------------------------------------------- *)

