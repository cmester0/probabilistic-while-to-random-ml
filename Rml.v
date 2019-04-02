From mathcomp Require Import all_ssreflect all_algebra.
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

Fixpoint lookup (p : (nat * Type)) (env : seq (nat * Type * Rml)) `{env_valid : valid_env env} :
  List.In p (map fst env) -> @sRml p.2.
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
    refine (@lookup (n,T) env env_valid H).
  - assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (sConst a).
  - destruct p.

    assert (x1_valid : rml_valid_type T x1 [seq i.1 | i <- env]) by (inversion x_valid ; subst ; assumption).
    
    pose (x1' := IHx1 T env env_valid x1_valid).

    pose (x1'' := sRml_to_rml x1').
    pose (x1''_simple := sRml_simple T x1').
    pose (x1''_valid := sRml_valid T x1').

    assert (x2_valid : rml_valid_type A x2 ((n,T) :: [seq i.1 | i <- env])) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((n,T,x1'') :: env)) by (constructor ; assumption).
    
    refine (IHx2 A ((n,T,x1'') :: env) env_valid' x2_valid).
  - assert (x1_valid : rml_valid_type bool x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A x3 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type bool x1 env env_valid x1_valid).
    pose (m1' := replace_all_variables_aux_type A x2 env env_valid x2_valid).
    pose (m2' := replace_all_variables_aux_type A x3 env env_valid x3_valid).

    pose (b'' := sRml_to_rml b').
    pose (m1'' := sRml_to_rml m1').
    pose (m2'' := sRml_to_rml m2').
    
    refine (rml_to_sRml (If_stm b'' m1'' m2'')).
    constructor ; eauto using sRml_simple.
    constructor ; eauto using sRml_valid.
    
  - assert (x1_valid : rml_valid_type (T -> A) x1 (map fst env)) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type T x2 (map fst env)) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type (T -> A) x1 env env_valid x1_valid).
    pose (e2' := replace_all_variables_aux_type T x2 env env_valid x2_valid).

    pose (e1'' := sRml_to_rml e1').
    pose (e2'' := sRml_to_rml e2').

    refine (rml_to_sRml (App_stm T e1'' e2'')).
    constructor ; eauto using sRml_simple.
    constructor ; eauto using sRml_valid.
Defined.

Definition replace_all_variables_type A (x : Rml) `{x_valid : rml_valid_type A x nil} :=
  @replace_all_variables_aux_type A x nil env_nil x_valid.

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

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x nil} : continuation_monad_type R A := interp_srml (@replace_all_variables_type A x x_valid).