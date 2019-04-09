From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.

(* -------------------------------------------------------------------------------- *)

Inductive Rml :=
| Var : (nat * Type) -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : (nat * Type) -> @Rml -> @Rml -> Rml
(* | Fun_stm : forall B, (nat * Type) -> B -> Rml -> Rml *)
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
                
| well_let_stm : forall x (e1 e2 : Rml) l,
    @well_formed l e1 ->
    @well_formed (x :: l) e2 ->
    well_formed l (Let_stm x e1 e2)
                
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
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml
| sFix : forall (B : Type) (C : Type), @sRml ((B -> C) -> B -> C) -> @sRml (((B -> C) -> B -> C) -> A) -> sRml.

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

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (@Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (@If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (@App_stm B e1 e2)
| is_fix : forall A B f x, rml_is_simple f -> rml_is_simple x -> rml_is_simple (@Let_rec A B f x).

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml_l {A : Type} (rml : Rml) `{rml_simple : @rml_is_simple rml} l `{rml_valid : @rml_valid_type A l rml} : @sRml A.
Proof.
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (A0 = A) by (inversion rml_valid ; subst ; reflexivity) ; subst.
    refine (sConst a).
  - exfalso.
    easy.
  - assert (if_valid_type : (rml_valid_type bool l r1 /\ rml_valid_type A l r2 /\ rml_valid_type A l r3)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.
    
    refine (sIf_stm (@rml_to_sRml_l bool r1 s1 l p1) (@rml_to_sRml_l A r2 s2 l p2) (@rml_to_sRml_l A r3 s3 l p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) l r1 /\ rml_valid_type T l r2) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : rml_is_simple r1 /\ rml_is_simple r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    apply (sApp_stm T (@rml_to_sRml_l (T -> A) r1 H1 l p1) (@rml_to_sRml_l T r2 H2 l p2)).
  - assert (rml_is_simple r1) by (inversion rml_simple ; assumption).
    assert (rml_valid_type p.2 [:: p0 , p & l] r1) by (inversion rml_valid ; assumption).
    pose (@rml_to_sRml_l p.2 r1 H [:: p0, p & l] H0).
Admitted.

Fixpoint rml_to_sRml {A : Type} (rml : Rml) `{rml_simple : @rml_is_simple rml} `{rml_valid : @rml_valid_type A nil rml} : @sRml A.
Proof.
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (A0 = A) by (inversion rml_valid ; subst ; reflexivity) ; subst.
    refine (sConst a).
  - exfalso.
    easy.
  - assert (if_valid_type : (rml_valid_type bool nil r1 /\ rml_valid_type A nil r2 /\ rml_valid_type A nil r3)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : rml_is_simple r1 /\ rml_is_simple r2 /\ rml_is_simple r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.
    
    refine (sIf_stm (@rml_to_sRml bool r1 s1 p1) (@rml_to_sRml A r2 s2 p2) (@rml_to_sRml A r3 s3 p3)).
  - assert (app_valid_type : rml_valid_type (T -> A) nil r1 /\ rml_valid_type T nil r2) by (intros ; inversion rml_valid ; easy).
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : rml_is_simple r1 /\ rml_is_simple r2) by (inversion rml_simple ; subst ; easy).
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    apply (sApp_stm T (@rml_to_sRml (T -> A) r1 H1 p1) (@rml_to_sRml T r2 H2 p2)).
  - assert (rml_is_simple r1) by (inversion rml_simple ; assumption).
    assert (rml_valid_type p.2 [:: p0; p] r1) by (inversion rml_valid ; assumption).
    
    pose (@rml_to_sRml p.2 (Let_stm p0 r2 (Let_stm p r1 r1))).
Admitted.

(* -------------------------------------------------------------------------------- *)

Fixpoint sRml_to_rml {A} (x : @sRml A) : Rml :=
  match x with
  | sConst c => Const A c
  | sIf_stm b m1 m2 => If_stm (sRml_to_rml b) (sRml_to_rml m1) (sRml_to_rml m2)
  | sApp_stm T e1 e2 => App_stm T (sRml_to_rml e1) (sRml_to_rml e2)
  | sFix B C f k => App_stm ((B -> C) -> B -> C) (sRml_to_rml k) (sRml_to_rml f)
  end.

Lemma sRml_simple :
  forall A (x : @sRml A),
    rml_is_simple (@sRml_to_rml A x).
Proof.
  induction x ; try (constructor ; easy).
Qed.

Lemma sRml_valid :
  forall A (x : @sRml A),
    rml_valid_type A nil (@sRml_to_rml A x).
Proof.
  induction x ; try (constructor ; easy).
Qed.

(** Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * Type * Rml) -> Prop :=
| env_nil : valid_env nil
| env_cons (x : nat * Type * Rml) xs :
    (rml_is_simple x.2) ->
    (rml_valid_type x.1.2 nil x.2) ->
    valid_env xs ->
    valid_env (x :: xs).

Fixpoint lookup (p : (nat * Type)) (env : seq (nat * Type * Rml)) `{env_valid : valid_env env} `{_ : List.In p (map fst env)} {struct env} : @sRml p.2.
  intros.
  induction env.
  - contradiction.
  - destruct (pselect (a.1 = p)).
    + intros.
      refine (rml_to_sRml a.2) ; inversion env_valid ; subst ; assumption.
    + intros.
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
    pose (x1''_simple := sRml_simple T x1').
    pose (x1''_valid := sRml_valid T x1').

    assert (x2_valid : rml_valid_type A ((n,T) :: [seq i.1 | i <- env]) x2) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((n,T,x1'') :: env)) by (constructor ; assumption).
    
    refine (IHx2 A ((n,T,x1'') :: env) env_valid' x2_valid).
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
  - destruct (pselect (A0 = A)).
    + subst.
      refine (Some (valid_const A l a)).
    + refine None.
  - destruct p.
    pose (ob (IHx1 l T) (fun valid_x1 =>
          ob (IHx2 ((n,T) :: l) A) (fun valid_x2 =>
          Some (valid_let A l T n x1 x2 valid_x1 valid_x2)))).
    apply o.
  - apply (ob (IHx1 l bool) (fun valid_x1 =>
          ob (IHx2 l A) (fun valid_x2 =>
          ob (IHx3 l A) (fun valid_x3 =>
          Some (valid_if A l x1 x2 x3 valid_x1 valid_x2 valid_x3))))).
  - apply (ob (IHx1 l (T -> A)) (fun valid_x1 =>
          ob (IHx2 l T) (fun valid_x2 =>
          Some (valid_app A l T x1 x2 valid_x1 valid_x2)))).
  - apply None.
Defined.
