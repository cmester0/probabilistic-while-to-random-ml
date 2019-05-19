From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.
Require Import Coq.Logic.Eqdep_dec.

(* -------------------------------------------------------------------------------- *)

Inductive Rml :=
| Var : (nat * Type) -> bool -> Rml (* bool = is fun var? *)
| Const : forall {A : Type}, A -> Rml
| Let_stm : (nat * Type) -> Rml -> Rml -> Rml
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml
| Let_rec : Type -> Type -> nat -> nat -> Rml -> Rml -> Rml
| Random : Rml -> Rml
| Flip : Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed (vl : seq (nat * Type)) (fl : seq (nat * Type)) : Rml -> Prop :=
| well_var : forall A x,
    List.In (x,A) vl ->
    well_formed vl fl (Var (x,A) false)

| well_fun_var : forall A x,
    List.In (x,A) fl ->
    well_formed vl fl (Var (x,A) true)
                
| well_const : forall A c,
    well_formed vl fl (@Const A c)
                
| well_let : forall x (e1 e2 : Rml),
    well_formed vl fl e1 ->
    well_formed (x :: vl) fl e2 ->
    well_formed vl fl (Let_stm x e1 e2)
                
| well_if : forall b m1 m2,
    well_formed vl fl b ->
    well_formed vl fl m1 ->
    well_formed vl fl m2 ->
    well_formed vl fl (If_stm b m1 m2)

| well_app : forall B e1 e2,
    well_formed vl fl e1 ->
    well_formed vl fl e2 ->
    well_formed vl fl (App_stm B e1 e2)

| well_let_rec : forall B C nf nx (e1 e2 : Rml),
    well_formed vl ((nx,B) :: (nf,B -> C) :: fl) e1 ->
    well_formed vl fl e2 ->
    well_formed vl fl (Let_rec B C nf nx e1 e2)

| well_random : forall e,
    well_formed vl fl e ->
    well_formed vl fl (Random e)

| well_flip :
    well_formed vl fl Flip.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type (A : Type) (vl : seq (nat * Type)) (fl : seq (nat * Type)) : Rml -> Prop :=
| valid_var : forall x,
    List.In (x,A) vl ->
    rml_valid_type A vl fl (Var (x,A) false)

| valid_fun_var : forall x,
    List.In (x,A) fl ->
    rml_valid_type A vl fl (Var (x,A) true)
                   
| valid_const : forall (c : A),
    rml_valid_type A vl fl (@Const A c)
                   
| valid_let : forall B x a b,
    @rml_valid_type B vl fl a ->
    @rml_valid_type A ((x,B) :: vl) fl b ->
    rml_valid_type A vl fl (Let_stm (x,B) a b)
                   
| valid_if : forall b m1 m2,
    rml_valid_type bool vl fl b ->
    rml_valid_type A vl fl m1 ->
    rml_valid_type A vl fl m2 ->
    rml_valid_type A vl fl (If_stm b m1 m2)
                   
| valid_app : forall (B : Type) e1 e2,
    rml_valid_type (B -> A) vl fl e1 ->
    rml_valid_type B vl fl e2 ->
    rml_valid_type A vl fl (App_stm B e1 e2)

| valid_let_rec : forall B nf nx e1 e2,
    @rml_valid_type A vl ((nx,B) :: (nf,B -> A) :: fl) e1 ->
    @rml_valid_type B vl fl e2 ->
    rml_valid_type A vl fl (Let_rec B A nf nx e1 e2)

| valid_random : forall e,
    A = nat ->
    rml_valid_type nat vl fl e ->
    rml_valid_type A vl fl (Random e)

| valid_flip :
    A = bool ->
    rml_valid_type A vl fl Flip.

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
Qed.

Definition ob :=
  fun {A B} (x : option A) (f : A -> option B) =>
    match x with
    | Some y => f y
    | None => None
    end.

(** * Simple Rml *) 
(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} :=
| sVar : nat -> sRml
| sConst : A -> sRml
| sIf : @sRml bool -> sRml -> sRml -> sRml
| sApp : forall T, @sRml (T -> A) -> @sRml T -> sRml
| sFix : forall B (nf nx : nat), @sRml A -> @sRml B -> sRml
| sRandom : (A = nat) -> @sRml nat -> sRml
| sFlip : (A = bool) -> sRml.

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple {l : seq (nat * Type)} : Rml -> Prop :=
| is_fun_var : forall (p : nat * Type),
    List.In p l -> rml_is_simple (Var p true)
                                                             
| is_const : forall (A : Type) c,
    rml_is_simple (@Const A c)
                                           
| is_if : forall b m1 m2,
    rml_is_simple b ->
    rml_is_simple m1 ->
    rml_is_simple m2 ->
    rml_is_simple (@If_stm b m1 m2)
                  
| is_app : forall (B : Type) e1 e2,
    rml_is_simple e1 ->
    rml_is_simple e2 ->
    rml_is_simple (@App_stm B e1 e2)
                  
| is_fix : forall B C nf nx e1 e2,
    @rml_is_simple [:: (nx,B), (nf,B -> C) & l] e1 ->
    @rml_is_simple l e2 ->
    rml_is_simple (@Let_rec B C nf nx e1 e2)

| is_random : forall e,
    rml_is_simple e ->
    rml_is_simple (Random e)

| is_flip :
    rml_is_simple Flip.

(* -------------------------------------------------------------------------------- *)

Fixpoint sRml_to_rml {A} (x : @sRml A) : Rml :=
  match x with
  | sVar n => Var (n,A) true
  | sConst c => @Const A c
  | sIf b m1 m2 => If_stm (sRml_to_rml b) (sRml_to_rml m1) (sRml_to_rml m2)
  | sApp T e1 e2 => App_stm T (sRml_to_rml e1) (sRml_to_rml e2)
  | sFix B nf nx f x =>
    Let_rec B A nf nx
            (sRml_to_rml f)
            (sRml_to_rml x)
  | sRandom A e => Random (sRml_to_rml e)
  | sFlip A => Flip
  end.

Inductive srml_valid_type (A : Type) (fl : seq (nat * Type)) : @sRml A -> Prop :=
| svalid_fun_var : forall x,
    List.In (x,A) fl ->
    srml_valid_type A fl (sVar x)
                   
| svalid_const : forall (c : A),
    srml_valid_type A fl (sConst c)
                   
| svalid_if : forall b m1 m2,
    srml_valid_type bool fl b ->
    srml_valid_type A fl m1 ->
    srml_valid_type A fl m2 ->
    srml_valid_type A fl (sIf b m1 m2)
                    
| svalid_app : forall (B : Type) e1 e2,
    @srml_valid_type (B -> A) fl e1 ->
    @srml_valid_type B fl e2 ->
    @srml_valid_type A fl (sApp B e1 e2)
                     
| svalid_fix : forall B nf nx f x,
    @srml_valid_type A ((nx,B) :: (nf,B -> A) :: fl) f ->
    @srml_valid_type B fl x ->
    srml_valid_type A fl (sFix B nf nx f x)

| svalid_random : forall e (H : A = nat),
    srml_valid_type nat fl e ->
    srml_valid_type A fl (sRandom H e)
                    
| svalid_flip : forall (H : A = bool),
    srml_valid_type A fl (sFlip H).

(** * Properties of sRml expressions *)

(* -------------------------------------------------------------------------------- *)

Require Import Eqdep_dec.

Lemma dec_eq : (forall x y : Type, {x = y} + {x <> y}).
Proof.
  (* decide equality. *)
Admitted.

Lemma helper :
  forall T A x1 x2 l, srml_valid_type A l (sApp T x1 x2) -> srml_valid_type (T -> A) l x1 /\ srml_valid_type T l x2.
  intros.
  inversion H.

  assert (e3 = x2) by apply (inj_pair2_eq_dec Type dec_eq [eta @sRml] T e3 x2 H3).
  assert (e0 = x1) by apply (inj_pair2_eq_dec Type dec_eq (fun T : Type => @sRml (forall _ : T, A)) T e0 x1 H1).
  subst ; clear H1 ; clear H3.  
  
  split ; assumption.
Qed.

Lemma helper2 :
  forall A B nx nf x1 x2 fl,
    srml_valid_type A fl (sFix B nf nx x1 x2) ->
    srml_valid_type A [:: (nx, B), (nf, B -> A) & fl] x1 /\
    srml_valid_type B fl x2.
  intros.
  inversion H.
  subst.

  (* assert (f0 = x1) by (apply (inj_pair2_eq_dec Type dec_eq) in H4 ; assumption). *)
  assert (x0 = x2) by (apply (inj_pair2_eq_dec Type dec_eq) in H5 ; assumption).
  
  subst.
  
  split ; assumption.
Qed.

Lemma srml_valid_weakening:
  forall (p : nat * Type) (x : @sRml p.2) l1 l2 l3, srml_valid_type p.2 (l1 ++ l3) x -> srml_valid_type p.2 (l1 ++ l2 ++ l3) x.
Proof.
  intros.
  generalize dependent l1.
  induction x ; intros.
  - inversion H.
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
  - constructor.
  - inversion H ; subst.
    constructor.
    + apply IHx1.
      assumption.
    + apply IHx2.
      assumption.
    + apply IHx3.
      assumption.
  - apply helper in H.
    inversion_clear H.
    + constructor.
      apply IHx1.
      assumption.
    + apply IHx2.
      assumption.
  - apply helper2 in H.
    inversion_clear H.
    constructor.
    + apply (IHx1 ([:: (nx, B), (nf, B -> A) & l1])).
      assumption.
    + apply IHx2.
      assumption.
  - inversion_clear H.
    constructor.
    apply IHx.    
    assumption.
  - constructor.
Qed.

Lemma sRml_simple :
  forall A (x : @sRml A) l (x_valid : srml_valid_type A l x),
    @rml_is_simple l (@sRml_to_rml A x).
Proof.
  induction x ; intros.
  (* sVar *)
  {
    inversion x_valid.
    constructor.
    assumption.
  }

  (* sConst *)
  { constructor. }

  (* sIf *)
  {
    inversion x_valid ; subst.
    constructor ; eauto 2.
  }

  (* sApp *)
  {
    apply helper in x_valid.
    inversion x_valid.
    constructor ; eauto 2.
  } 

  (* sFix *)
  {
    apply helper2 in x_valid.
    inversion_clear x_valid.
    simpl.
    constructor.
    - apply IHx1.
      assumption.
    - apply IHx2.
      assumption.
  }

  (* sRandom *)
  {
    inversion_clear x_valid.
    simpl.
    constructor.
    apply IHx.
    assumption.
  }

  (* sFlip *)
  {
    constructor.
  }
Qed.

Lemma sRml_valid :
  forall A (x : @sRml A) vl fl (x_valid : srml_valid_type A fl x),
    rml_valid_type A vl fl (@sRml_to_rml A x).
Proof.
  induction x ; intros.
  (* sVar *)
  {
    simpl.
    inversion x_valid.
    constructor 2.
    assumption.
  }

  (* sConst *)
  { constructor. }

  (* sIf *)
  {
    simpl.
    inversion x_valid.
    constructor ; eauto.
  }

  (* sApp *)
  {
    simpl.
    apply helper in x_valid.
    inversion x_valid.
    constructor ; eauto.
  }

  (* sFix *)
  {
    apply helper2 in x_valid.
    inversion_clear x_valid.

    apply IHx1 with (vl := vl) in H.
    apply IHx2 with (vl := vl) in H0.
    
    simpl.
    constructor.
    - assumption.
    - assumption.
  }

  (* sRandom *)
  {
    inversion_clear x_valid.
    
    simpl.
    constructor.
    assumption.
    apply IHx.

    assumption.
  }

  (* sFlip *)
  {
    constructor.
    assumption.
  }
Qed.

(** * Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * Type * Rml) -> seq (nat * Type) -> Prop :=
| env_nil l : valid_env nil l
| env_cons (x : nat * Type * Rml) xs l :
    (@rml_is_simple l x.2) ->
    (@rml_valid_type x.1.2 (map fst xs) l x.2) ->
    valid_env xs l ->
    valid_env (x :: xs) l.

(* Inductive valid_env : seq (nat * Type * Rml) -> seq (nat * Type) -> Prop := *)
(* | env_nil l : valid_env nil l *)
(* | env_cons (x : nat * Type * Rml) xs l : *)
(*     (@rml_is_simple l x.2) -> *)
(*     (@rml_valid_type x.1.2 (map fst xs) l x.2) -> *)
(*     valid_env xs l -> *)
(*     valid_env (x :: xs) l. *)

Lemma valid_weakening:
  forall (a : nat * Type * Rml) l1 l2 l3 fl, rml_valid_type a.1.2 (l1 ++ l3) fl a.2 -> rml_valid_type a.1.2 (l1 ++ l2 ++ l3) fl a.2.
Proof.
  intros.
  destruct a.
  destruct p.
  simpl in *.
  generalize dependent fl.
  generalize dependent T.
  generalize dependent l1.
  induction r ; intros.
  (* Var *)
  {
    inversion H ; subst.
    + constructor.
      apply List.in_app_or in H1.
      inversion H1.
      * apply List.in_or_app.
        left.
        assumption.
      * apply List.in_or_app.
        right.
        apply List.in_or_app.
        right.
        assumption.
    + constructor 2.
      assumption.
  }

  (* Const *)
  {
    inversion H ; subst.
    constructor.
  }
  
  (* Let *)
  {
    inversion H ; subst.
    constructor.
    * apply IHr1.
      assumption.
    * apply (IHr2 ((x,B) :: l1)).
      assumption.
  }

  (* If *)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (* App *)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (* Let_rec *)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (* Random *)
  {
    inversion H ; subst.
    constructor.
    reflexivity.
    apply IHr.
    assumption.
  }

  (* Flip *)
  {
    inversion H ; subst.
    constructor.
    reflexivity.
  }
Qed.

Corollary valid_weakening_nil :
  forall (a : nat * Type * Rml) l1 l2 fl, rml_valid_type a.1.2 (l1) fl a.2 -> rml_valid_type a.1.2 (l1 ++ l2) fl a.2.
Proof.
  intros.  
  pose (valid_weakening a l1 l2 nil%SEQ).
  rewrite <- (cats0 (l1 ++ l2)).
  rewrite <- catA.
  apply r.
  rewrite cats0.
  assumption.
Qed.

Lemma valid_weakening_fl :
  forall (a : nat * Type * Rml) l1 l2 l3 vl, rml_valid_type a.1.2 vl (l1 ++ l3) a.2 -> rml_valid_type a.1.2 vl (l1 ++ l2 ++ l3) a.2.
Proof.
  intros.
  destruct a.
  destruct p.
  simpl in *.
  generalize dependent vl.
  generalize dependent T.
  generalize dependent l1.
  induction r ; intros.
  (* Var *)
  {
    inversion H ; subst.
    + constructor.
      assumption.
    + constructor 2.
      apply List.in_app_or in H1.
      inversion H1.
      * apply List.in_or_app.
        left.
        assumption.
      * apply List.in_or_app.
        right.
        apply List.in_or_app.
        right.
        assumption.
  }

  (* Const *)
  {
    inversion H.
    constructor.
  }

  (* Let *)
  {
    inversion H ; subst.
    constructor.
    + apply IHr1.
      assumption.
    + apply IHr2.
      assumption.
  }

  (* If *)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (* App *)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (* Let_rec *)
  {
    inversion H ; subst.
    constructor ; eauto.
    inversion H ; subst.
    apply (IHr1 [:: (n1,T) , (n0,T -> T0) & l1]).
    assumption.
  }

  (* Random *)
  {
    inversion H ; subst.
    constructor.
    reflexivity.
    apply IHr.
    assumption.
  }

  (* Flip *)
  {
    inversion H ; subst.
    constructor.
    reflexivity.
  }
Qed.

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml_l {A : Type} (x : Rml) vl fl `{rml_simple : @rml_is_simple fl x} `{rml_valid : @rml_valid_type A vl fl x} {struct x} : @sRml A.
Proof.
  (** Structure **)
  case x eqn : o_rml.
  { exact (sVar p.1). }
  
  (** Const **)
  {
    assert (A0 = A) by (inversion rml_valid ; subst ; reflexivity) ; subst.
    exact (sConst a).
  }

  (** Let **)
  { exfalso ; easy. }

  (** If *)
  {
    assert (if_valid_type : (rml_valid_type bool vl fl r1 /\ rml_valid_type A vl fl r2 /\ rml_valid_type A vl fl r3)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : @rml_is_simple fl r1 /\ @rml_is_simple fl r2 /\ @rml_is_simple fl r3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.

    exact (sIf (@rml_to_sRml_l bool r1 vl fl s1 p1) (@rml_to_sRml_l A r2 vl fl s2 p2) (@rml_to_sRml_l A r3 vl fl s3 p3)).
  }

  (** App *)
  {    
    assert (app_valid_type : rml_valid_type (T -> A) vl fl r1 /\ rml_valid_type T vl fl r2) by (inversion rml_valid ; subst ; split ; try constructor ; easy).
    
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : @rml_is_simple fl r1 /\ @rml_is_simple fl r2) by (inversion rml_simple ; subst ; split ; try easy ; constructor ; assumption).
    
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.
    
    exact (sApp T (@rml_to_sRml_l (T -> A) r1 vl fl H1 p1) (@rml_to_sRml_l T r2 vl fl H2 p2)).
  }

  (** Let rec **)
  {
    
    assert (@rml_is_simple [:: (n0,T) , (n,T -> T0) & fl] r1 /\ @rml_is_simple fl r2) by (inversion rml_simple ; subst ; easy).
        
    inversion_clear H.
    
    assert (rml_valid_type T0 vl [:: (n0,T), (n,T -> T0) & fl] r1 /\ rml_valid_type T vl fl r2) by (inversion rml_valid ; inversion H8 ; subst ; easy).

    inversion_clear H.
    
    pose (rml_to_sRml_l T0 r1 vl ((n0,T) :: (n,T -> T0) :: fl) H0 H2).
    pose (rml_to_sRml_l T r2 vl fl H1 H3).

    assert (A = T0) by (inversion rml_valid ; reflexivity) ; subst.
    
    exact (sFix T n n0 s s0).
  }

  (** Random **)
  {
    assert (@rml_is_simple fl r) by (inversion rml_simple ; assumption).
    assert (rml_valid_type nat vl fl r) by (inversion rml_valid ; assumption).
    assert (A = nat) by (inversion rml_valid ; assumption).
    
    pose (rml_to_sRml_l nat r vl fl H H0).
    exact (sRandom H1 s).
  }

  (** Flip **)
  {
    assert (A = bool) by (inversion rml_valid ; assumption).
    exact (sFlip H).    
  }
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint lookup (p : (nat * Type)) (env : seq (nat * Type * Rml)) (fl : seq (nat * Type)) `{env_valid : valid_env env fl} `{_ : List.In p (map fst env) \/ List.In p fl} {struct env} : @sRml p.2.
  intros.
  induction env.
  - refine (sVar p.1).
  - destruct (pselect (a.1 = p)).
    + intros.
      refine (rml_to_sRml_l a.2 (map fst env) fl) ; inversion env_valid ; subst.
      * assumption.
      * assumption.
    + apply IHenv.
      * inversion env_valid ; subst ; assumption.
      * inversion H ; subst.
        -- left.
           inversion H0 ; easy.
        -- right.
           assumption.
Defined.

Lemma rml_simple_weakening :
  forall x l1 l2 l3, @rml_is_simple (l1 ++ l3) x -> @rml_is_simple (l1 ++ l2 ++ l3) x.
Proof.
  induction x ; intros.
  (** Var **)
  {
    inversion H ; subst.
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
  }

  (** Const **)
  { constructor. }

  (** Let **)
  { inversion H. }

  (** If **)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (** App **)
  {
    inversion H ; subst.
    constructor ; eauto.
  }

  (** Let rec **)
  {
    inversion H ; subst.
    constructor.
    - apply (IHx1 ((n0,T) :: (n,T -> T0) :: l1) l2 l3).
      assumption.
    - apply IHx2.
      assumption.
  }

  (** Random *)
  {
    inversion H ; subst.
    constructor.
    apply IHx.
    assumption.
  }

  (** Flip **)
  {
    constructor.
  }
Qed.    

Lemma extend_fl_still_valid :
  forall p env fl, valid_env env fl -> valid_env env (p :: fl).
Proof.
  intros.
  induction env.
  - constructor.
  - inversion H ; subst.
    constructor.
    + apply (rml_simple_weakening a.2 nil [:: p] fl).
      assumption.
    + apply (valid_weakening_fl a nil [:: p] fl).
      assumption.
    + apply IHenv.
      assumption.
Qed.  


(* EXAMPLE *)

Inductive correctness {A} : @sRml A -> Rml -> Prop :=
| correct_var : forall n,
    correctness (sVar n) (Var (n,A) true)
                
| correct_const : forall c,
    correctness (sConst c) (@Const A c)
                
| correct_if : forall b b' m1 m1' m2 m2',
    @correctness bool b b' ->
    correctness m1 m1' ->
    correctness m2 m2' ->
    correctness (sIf b m1 m2) (If_stm b' m1' m2')
| correct_app : forall T e1 e1' e2 e2',
    @correctness (T -> A) e1 e1' ->
    @correctness T e2 e2' ->
    correctness (sApp T e1 e2) (App_stm T e1' e2')
                
| correct_rec : forall B f f' x x' nf nx,
    @correctness B x x' ->
    correctness f f' ->
    correctness (sFix B nf nx f x) (Let_rec B A nf nx f' x')
                
| correct_random : forall e e' (H : A = nat),
    @correctness nat e e' ->
    correctness (sRandom H e) (Random e')
                
| correct_flip : forall (H : A = bool),
    correctness (sFlip H) (Flip).

Theorem srml_to_rml_correctness :
  forall A (x : @sRml A), @correctness A x (sRml_to_rml x).
Proof.
  induction x ; simpl ; constructor ; assumption.
Qed.

Lemma correct_is_simple :
  forall A x y vl fl, @rml_valid_type A vl fl x -> @correctness A y x -> @rml_is_simple fl x.
Proof.
  intros.
  generalize dependent x.
  generalize dependent fl.
  induction y ; intros.
  (* sVar *)
  {
    inversion H0 ; subst.
    inversion H ; subst.
    constructor.
    assumption.
  }

  (* sConst *)
  {
    inversion H0 ; subst.
    constructor.
  }

  (* if *)
  {
    inversion H0 ; subst.
    inversion H ; subst.
    constructor ; eauto.
  }
  
  (* app *)
  {
    inversion H0 ; subst.
    inversion H ; subst.
    apply (inj_pair2_eq_dec Type dec_eq) in H2.
    apply (inj_pair2_eq_dec Type dec_eq) in H4.
    subst.
    simpl.
    constructor ; eauto.
  }

  (* fix *)
  {
    inversion H0 ; subst.
    inversion H ; subst.
    apply (inj_pair2_eq_dec Type dec_eq) in H6.
    subst.
    constructor ; eauto.
  }

  (* random *)
  {
    inversion H0 ; subst.
    inversion H ; subst.
    constructor ; eauto.
  }

  (* flip *)
  {
    inversion H0 ; subst.
    constructor.
  }
Qed.

Definition asdf : Rml :=
  Let_stm (4,nat <: Type) (Const 100) (Var (4,nat <: Type) false).

Definition asdf2 : Rml := (Const 100).

Fixpoint count_let (x : Rml) : nat :=
  match x with
  | Var _ _ | @Const _ _ | Flip => 0
  | Let_stm _ a b => 1 + count_let a + count_let b
  | If_stm a b c => count_let a + count_let b + count_let c
  | App_stm _ a b => count_let a + count_let b
  | Let_rec _ _ _ _ a b => count_let a + count_let b
  | Random a => count_let a
  end.

Theorem sum_to_zero :
  forall x y,
    x + y = 0 <-> x = 0 /\ y = 0.
Proof. induction x ; easy. Qed.    

Theorem zero_let_is_simple :
  forall A x fl (x_valid : rml_valid_type A nil fl x),
    count_let x = 0 -> @rml_is_simple fl x.
Proof.
  intros.
  generalize dependent fl.
  generalize dependent A.
  induction x ; intros.
  - inversion x_valid ; subst.
    + contradiction.
    + constructor.
      assumption.
  - constructor.
  - inversion H. (* contradiction *)
  - inversion x_valid ; subst.
    inversion H.
    apply sum_to_zero in H1.
    inversion_clear H1.
    apply sum_to_zero in H0.
    inversion_clear H0.
    apply (IHx1 H1) in H3.
    apply (IHx2 H6) in H4.
    apply (IHx3 H2) in H5.
    
    constructor ; assumption.

  - inversion x_valid ; subst.
    inversion H.
    apply sum_to_zero in H1.
    inversion_clear H1.
    apply (IHx1 H0) in H2.
    apply (IHx2 H3) in H4.
    
    constructor ; assumption.
    
  - inversion x_valid ; subst.
    inversion H.
    apply sum_to_zero in H1.
    inversion_clear H1.
    apply (IHx1 H0) in H2.
    apply (IHx2 H3) in H7.
    constructor ; assumption.

  - constructor.
    inversion H.
    inversion x_valid ; subst.
    apply (IHx H1 nat).
    assumption.

  - constructor.
Qed.

(* END *)

Lemma back_no_lets :
  forall A x, count_let (@sRml_to_rml A x) = 0.
Proof.
  intros.
  induction x.
  - constructor.
  - constructor.
  - simpl.
    apply sum_to_zero.
    split.
    apply sum_to_zero.
    split.
    assumption.
    assumption.
    assumption.
  - simpl.
    apply sum_to_zero.
    split ; assumption.
  - simpl.
    apply sum_to_zero.
    split ; assumption.
  - simpl.
    assumption.
  - simpl.
    reflexivity.
Qed.    

Fixpoint count_false_var (x : Rml) : nat :=
  match x with
  | Var _ false => 1
  | Var _ true | @Const _ _ | Flip => 0
  | Let_stm _ a b => count_false_var a + count_false_var b
  | If_stm a b c => count_false_var a + count_false_var b + count_false_var c
  | App_stm _ a b => count_false_var a + count_false_var b
  | Let_rec _ _ _ _ a b => count_false_var a + count_false_var b
  | Random a => count_false_var a
  end.

Lemma back_no_false_var :
  forall A x, count_false_var (@sRml_to_rml A x) = 0.
Proof.
  intros.
  induction x.
  - constructor.
  - constructor.
  - simpl.
    apply sum_to_zero.
    split.
    apply sum_to_zero.
    split.
    assumption.
    assumption.
    assumption.
  - simpl.
    apply sum_to_zero.
    split ; assumption.
  - simpl.
    apply sum_to_zero.
    split ; assumption.
  - simpl.
    assumption.
  - simpl.
    reflexivity.
Qed.

Lemma simple_if_well :
  forall fl x,
    well_formed nil fl x ->
    count_false_var x = 0 ->
    count_let x = 0 ->
    @rml_is_simple fl x.
Proof.
  intros.
  generalize dependent fl.
  induction x ; intros.
  - inversion H ; subst.
    + contradiction.
    + constructor.
      assumption.
  - constructor.
  - inversion H1.
  - inversion H ; subst.
    inversion H1.
    inversion H0.
    apply sum_to_zero in H3.
    inversion_clear H3.
    apply sum_to_zero in H2.
    inversion_clear H2.
    apply sum_to_zero in H4.
    inversion_clear H4.
    apply sum_to_zero in H2.
    inversion_clear H2.        
    constructor ; eauto.
  - inversion H ; subst.
    inversion H1.
    inversion H0.
    apply sum_to_zero in H3.
    inversion_clear H3.
    apply sum_to_zero in H5.
    inversion_clear H5.
    constructor ; eauto.
  - inversion H ; subst.
    inversion H1.
    inversion H0.
    apply sum_to_zero in H3.
    inversion_clear H3.
    apply sum_to_zero in H5.
    inversion_clear H5.
    constructor ; eauto.
  - inversion H ; subst.
    inversion H1.
    inversion H0.
    constructor ; eauto.
  - constructor.
Qed.
    
Fixpoint replace_all_variables_aux_type
         A (x : Rml) (env : seq (nat * Type * Rml))
         (fl : seq (nat * Type)) `{env_valid : valid_env env fl}
         `{x_valid : @rml_valid_type A (map fst env) fl x} {struct x} : @sRml A.
Proof.
  (** Structure **)
  generalize dependent fl.
  generalize dependent env.
  generalize dependent A.
  induction x ; intros.
  (** Var *)
  {
    assert (List.In p (map fst env) \/ List.In p fl) by (inversion x_valid ; subst ; auto).
    destruct p.
    assert (A = T) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (@lookup (n,T) env fl env_valid H).
  }

  (** Const **)
  {
    assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (sConst a).
  }
      
  (** Let-stm **)
  {
    assert (x1_valid : rml_valid_type p.2 [seq i.1 | i <- env] fl x1) by (inversion x_valid ; subst ; assumption).

    pose (x1' := replace_all_variables_aux_type p.2 x1 env fl env_valid x1_valid).
    pose (x1'' := @sRml_to_rml p.2 x1').

    assert (correctness x1' x1'') by apply (@srml_to_rml_correctness p.2 x1').

    pose (correct_is_simple p.2 x1'' x1' (map fst env) fl).

    
    
    pose (x1''' := replace_all_variables_aux_type p.2 x1'' env fl env_valid x1_valid).

    
    pose (@rml_to_sRml_l p.2 x1'' (map fst env) fl).
    
    assert (replace_correct : correctness x1' x1).
    unfold x1'.
    induction x1.
    - 
    
    pose (x1_simple := correct_is_simple p.2 x1 x1' (map fst env) fl x1_valid replace_correct).
    
    assert (x2_valid : rml_valid_type A (p :: [seq i.1 | i <- env]) fl x2) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((p,x1) :: env) fl) by (constructor ; assumption).
    
    refine (replace_all_variables_aux_type A x2 ((p,x1) :: env) fl env_valid' x2_valid).
  }
    
  (** If-stm **)
  {
    assert (x1_valid : rml_valid_type bool (map fst env) fl x1) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A (map fst env) fl x2) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A (map fst env) fl x3) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type bool x1 env fl env_valid x1_valid).
    pose (m1' := replace_all_variables_aux_type A x2 env fl env_valid x2_valid).
    pose (m2' := replace_all_variables_aux_type A x3 env fl env_valid x3_valid).

    pose (b'' := sRml_to_rml b').
    pose (m1'' := sRml_to_rml m1').
    pose (m2'' := sRml_to_rml m2').

    pose (b_valid := valid_rml_makes_valid_srml bool x1 b' [seq i.1 | i <- env] fl x1_valid).
    pose (m1_valid := valid_rml_makes_valid_srml A x2 m1' [seq i.1 | i <- env] fl x2_valid).
    pose (m2_valid := valid_rml_makes_valid_srml A x3 m2' [seq i.1 | i <- env] fl x3_valid).
    
    refine (rml_to_sRml_l (If_stm b'' m1'' m2'') [seq i.1 | i <- env] fl).
    constructor ; eauto using sRml_simple.
    constructor ; eauto using sRml_valid.
  }

  (** App-stm **)
  {
    assert (x1_valid : rml_valid_type (T -> A) (map fst env) fl x1) by (inversion x_valid ; subst ; assumption).
        
    assert (x2_valid : rml_valid_type T (map fst env) fl x2) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type (T -> A) x1 env fl env_valid x1_valid).
    pose (e2' := replace_all_variables_aux_type T x2 env fl env_valid x2_valid).

    pose (e1'' := sRml_to_rml e1').
    pose (e2'' := sRml_to_rml e2').

    pose (b_valid := valid_rml_makes_valid_srml (T -> A) x1 e1' [seq i.1 | i <- env] fl x1_valid).
    pose (m1_valid := valid_rml_makes_valid_srml T x2 e2' [seq i.1 | i <- env] fl x2_valid).
    
    refine (rml_to_sRml_l (App_stm T e1'' e2'') [seq i.1 | i <- env] fl).
    constructor ; eauto 2 using sRml_simple.
    constructor ; eauto 2 using sRml_valid.
  }

  (** Let rec **)
  {
    pose (fl_x1 := [:: (n0, T), (n, T -> T0) & fl]).
    
    assert (x1_valid : rml_valid_type A [seq i.1 | i <- env] fl_x1 x1) by (inversion x_valid ; subst ; assumption).
    
    assert (x2_valid : rml_valid_type T [seq i.1 | i <- env] fl x2) by (inversion x_valid ; subst ; assumption).

    
    assert (env_valid_x1 : valid_env env fl_x1) by (repeat apply extend_fl_still_valid ; assumption).
    
    pose (x1' := replace_all_variables_aux_type A x1 env fl_x1 env_valid_x1 x1_valid).
    assert (env_valid_x2 : valid_env env fl) by (repeat apply extend_fl_still_valid ; assumption).
    
    pose (x2' := replace_all_variables_aux_type T x2 env fl env_valid_x2 x2_valid).    
    
    refine (sFix T n n0 x1' x2').
  }

  (** Random **)
  {
    assert (rml_valid_type nat (map fst env) fl x) by (inversion x_valid ; assumption).

    pose (replace_all_variables_aux_type nat x env fl env_valid H).

    assert (A = nat) by (inversion x_valid ; assumption).
    
    refine (sRandom H0 s).
  }

  (** Flip **)
  {
    assert (A = bool) by (inversion x_valid ; assumption).
    refine (sFlip H).
  }
Defined.

Definition replace_all_variables_type A (x : Rml) `{x_valid : rml_valid_type A nil nil x} :=
  @replace_all_variables_aux_type A x nil nil (env_nil nil) x_valid.

(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall (x : Rml) A vl fl `{x_valid : rml_valid_type A vl fl x},
    well_formed vl fl x.
Proof.
  induction x ; intros.

  6: {
    inversion x_valid ; subst.
    constructor ; eauto.
  }

  all: inversion x_valid ; subst ; try (apply well_fun_var ; assumption) ; try (constructor ; eauto).
Qed.

(* -------------------------------------------------------------------------------- *) 