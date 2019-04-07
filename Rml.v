From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.

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
Qed.

(* -------------------------------------------------------------------------------- *)

Fixpoint sRml_to_rml {A} (x : @sRml A) : Rml :=
  match x with
  | sConst c => Const A c
  | sIf_stm b m1 m2 => If_stm (sRml_to_rml b) (sRml_to_rml m1) (sRml_to_rml m2)
  | sApp_stm T e1 e2 => App_stm T (sRml_to_rml e1) (sRml_to_rml e2)
  end.

Lemma sRml_simple :
  forall A (x : @sRml A),
    rml_is_simple (@sRml_to_rml A x).
Proof.
  intros.
  induction x.
  - constructor.
  - constructor ; assumption.
  - constructor ; assumption.
Qed.

Lemma sRml_valid :
  forall A (x : @sRml A),
    rml_valid_type A (@sRml_to_rml A x) nil.
Proof.
  intros.
  induction x.
  - constructor.
    reflexivity.
  - constructor ; assumption.
  - constructor ; assumption.
Qed.

(** Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * Type * Rml) -> Prop :=
| env_nil : valid_env nil
| env_cons (x : nat * Type * Rml) xs :
    (rml_is_simple x.2) ->
    (rml_valid_type x.1.2 x.2 nil) ->
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

Fixpoint replace_all_variables_aux_type A (x : Rml) (env : seq (nat * Type * Rml))
         `{env_valid : valid_env env} `{x_valid : @rml_valid_type A x (map fst env)} : @sRml A.
Proof.
  generalize dependent env.
  generalize dependent A.
  induction x ; intros.
  - assert (List.In p (map fst env)) by (inversion x_valid ; subst ; easy).
    destruct p.
    assert (A = T) by (inversion x_valid ; subst ; reflexivity) ; subst.
    exact (@lookup (n,T) env env_valid H).
  - assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    exact (sConst a).
  - destruct p.

    assert (x1_valid : rml_valid_type T x1 [seq i.1 | i <- env]) by (inversion x_valid ; subst ; assumption).
    
    pose (x1' := IHx1 T env env_valid x1_valid).

    pose (x1'' := sRml_to_rml x1').
    pose (x1''_simple := sRml_simple T x1').
    pose (x1''_valid := sRml_valid T x1').

    assert (x2_valid : rml_valid_type A x2 ((n,T) :: [seq i.1 | i <- env])) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((n,T,x1'') :: env)) by (constructor ; assumption).
    
    exact (IHx2 A ((n,T,x1'') :: env) env_valid' x2_valid).
  - assert (x1_valid : rml_valid_type bool x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A x3 (map fst env)) by (inversion x_valid ; subst ; assumption).
        
    refine (rml_to_sRml (If_stm (sRml_to_rml (replace_all_variables_aux_type bool x1 env env_valid x1_valid)) (sRml_to_rml (replace_all_variables_aux_type A x2 env env_valid x2_valid)) (sRml_to_rml (replace_all_variables_aux_type A x3 env env_valid x3_valid)))).
    constructor ; apply sRml_simple.
    constructor ; apply sRml_valid.
    
  - assert (x1_valid : rml_valid_type (T -> A) x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type T x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    refine (rml_to_sRml (App_stm T (sRml_to_rml (replace_all_variables_aux_type (T -> A) x1 env env_valid x1_valid)) (sRml_to_rml (replace_all_variables_aux_type T x2 env env_valid x2_valid)))).
    constructor ; apply sRml_simple.
    constructor ; apply sRml_valid.
Defined.


Fixpoint lookup_alt (p : (nat * Type)) (env : seq (nat * Type * Rml)) {struct env} : option (Rml).
  intros.
  induction env.
  - refine None.
  - destruct (pselect (a.1 = p)).
    + intros.
      refine (Some a.2).
    + intros.
      apply IHenv.
Defined.

Definition ob {A B} (x : option A) (f : A -> option B) : option B :=
  match x with
  | Some y => f y
  | None => None
  end.
Notation "x >>= f" := (ob x f) (at level 40, left associativity).

Fixpoint replace_all_variables_aux_type_alt A (x : Rml) (env : seq (nat * Type * Rml)) {struct x} : option Rml :=
  match x with
  | Var p =>
    if pselect (p.2 = A)
    then lookup_alt (p.1,A) env
    else None
  | Const T c =>
    if pselect (T = A)
    then Some x
    else None
  | Let_stm p a b =>
    replace_all_variables_aux_type_alt A b ((p,a) :: env) >>= (fun b' =>
    replace_all_variables_aux_type_alt p.2 a env >>= (fun a' =>
    Some (Let_stm p b' a')))
  | If_stm b m1 m2 =>
    replace_all_variables_aux_type_alt bool b env >>= (fun b' =>
    replace_all_variables_aux_type_alt A m1 env >>= (fun m1' =>
    replace_all_variables_aux_type_alt A m2 env >>= (fun m2' =>
    Some (If_stm b' m1' m2'))))
  | App_stm T e1 e2 =>
    replace_all_variables_aux_type_alt (T -> A) e1 env >>= (fun e1' =>
    replace_all_variables_aux_type_alt T e2 env >>= (fun e2' =>
    Some (App_stm T e1' e2')))
  end.

Lemma lookup_alt_if_in :
  forall p env y,
    lookup_alt p env = Some y ->
    List.In p (map fst env).
Proof.
  intros.
  induction env.
  - inversion H. (* contradiction. *)
  - simpl in H.
    simpl.
    destruct pselect.
    + left ; assumption.
    + right. apply IHenv.
      unfold list_rect in H.
      rewrite <- H.
      induction env.
      * simpl.
        reflexivity.
      * simpl in *.
        reflexivity.
Qed.  
      
Theorem replace_alt_is_also_valid :
  forall A x env y `{env_valid : valid_env env},
    replace_all_variables_aux_type_alt A x env = Some y ->
    exists x_valid y_simple y_valid,
      @replace_all_variables_aux_type A x env env_valid x_valid = @rml_to_sRml A y y_simple y_valid.
Proof.
  induction x ; intros.
  - simpl in H.
    destruct pselect.
    + simpl in H.
      assert (List.In (p.1,p.2) (map fst env)).
      * apply lookup_alt_if_in with (y := y).
        subst.
        assumption.
      * subst.
        rewrite (surjective_pairing p).
        exists (valid_var p.1 (map fst env) p.2 H0).

        simpl snd.
        induction env.
        -- contradiction.
        -- inversion env_valid ; subst.
           inversion H.
           destruct pselect.
           ++ inversion H2.
              subst.
              exists H3.
              destruct a.
              simpl in e.
              simpl snd.
              simpl in H4.
              rewrite <- surjective_pairing in e.
              subst.              
              exists H4.


              
              destruct p.
              simpl.
              destruct pselect.
              simpl.
              induction env.
              simpl.
              unfold eq_rect_r.
              unfold eq_rect.
              unfold Logic.eq_sym.
              unfold eq_ind_r.
              unfold eq_ind.
              unfold Logic.eq_sym.
              unfold f_equal.

              
      
  

Compute replace_all_variables_aux_type_alt nat (Let_stm (4,_) (Const nat 2) (Var (4,_))) nil.

Compute (@replace_all_variables_aux_type nat (Let_stm (4,_) (Const nat 2) (Var (4,_))) nil env_nil (valid_let nat nat 4 (Const nat 2) (Var (4,_)) nil (@valid_const nat nat 2 (@erefl Type nat) nil) (valid_var 4 [:: (4,_)] nat _))).

Fixpoint valid_normal_form A (x : Rml) (env : seq (nat * Type)) `{rml_valid_type A x env} : rml_valid_type A x env.
Proof.
  induction x ; intros.
  - destruct p.
    inversion rml_valid_type0 ; subst.
    apply (valid_var n env T).
    assumption.
  - constructor.
    inversion rml_valid_type0 ; subst.
    reflexivity.
  - inversion rml_valid_type0 ; subst.
    constructor.    
    apply (valid_normal_form B x1 env H4).
    apply (valid_normal_form A x2 ((x,B) :: env) H5).
  - inversion rml_valid_type0 ; subst.
    constructor.
    apply (valid_normal_form bool x1 env H3).
    apply (valid_normal_form A x2 env H5).
    apply (valid_normal_form A x3 env H6).
  - inversion rml_valid_type0 ; subst.
    constructor.
    apply (valid_normal_form (T -> A) x1 env H4).
    apply (valid_normal_form T x2 env H5).
Defined.

Compute (valid_normal_form nat (Let_stm (2,_) (Const nat 4) (Var (2,_))) nil).
  
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
Qed.

(* -------------------------------------------------------------------------------- *)