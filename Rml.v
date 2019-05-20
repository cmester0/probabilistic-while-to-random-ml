From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.
Require Import Coq.Logic.Eqdep_dec.

Require Import Eqdep_dec.

(* -------------------------------------------------------------------------------- *)

Inductive Rml :=
| Var : (nat * choiceType) -> bool -> Rml (* bool = is fun var? *)
| Const : forall {A : choiceType}, A -> Rml
| Let_stm : (nat * choiceType) -> Rml -> Rml -> Rml
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : choiceType -> Rml -> Rml -> Rml
| Let_rec : choiceType -> choiceType -> nat -> nat -> Rml -> Rml -> Rml
| Random : Rml -> Rml
| Flip : Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed (vl : seq (nat * choiceType)) (fl : seq (nat * choiceType)) : Rml -> Prop :=
| well_var : forall p,
    List.In p vl ->
    well_formed vl fl (Var p false)

| well_fun_var : forall p,
    List.In p fl ->
    well_formed vl fl (Var p true)
                
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

| well_let_rec : forall (B C : choiceType) nf nx (e1 e2 : Rml),
    well_formed vl ((nx,B) :: (nf,prod_choiceType B C) :: fl) e1 ->
    well_formed vl fl e2 ->
    well_formed vl fl (Let_rec B C nf nx e1 e2)

| well_random : forall e,
    well_formed vl fl e ->
    well_formed vl fl (Random e)

| well_flip :
    well_formed vl fl Flip.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type : choiceType -> seq (nat * choiceType) -> seq (nat * choiceType) -> Rml -> Prop :=
| valid_var : forall vl fl p,
    List.In p vl ->
    rml_valid_type p.2 vl fl (Var p false)

| valid_fun_var : forall vl fl p,
    List.In p fl ->
    rml_valid_type p.2 vl fl (Var p true)
                   
| valid_const : forall (A : choiceType) vl fl (c : A),
    rml_valid_type A vl fl (@Const A c)
                   
| valid_let : forall A vl fl p a b,
    @rml_valid_type p.2 vl fl a ->
    @rml_valid_type A (p :: vl) fl b ->
    rml_valid_type A vl fl (Let_stm p a b)
                   
| valid_if : forall A vl fl b m1 m2,
    rml_valid_type bool_choiceType vl fl b ->
    rml_valid_type A vl fl m1 ->
    rml_valid_type A vl fl m2 ->
    rml_valid_type A vl fl (If_stm b m1 m2)
                   
| valid_app : forall A vl fl (B : choiceType) e1 e2,
    rml_valid_type (prod_choiceType B A) vl fl e1 ->
    rml_valid_type B vl fl e2 ->
    rml_valid_type A vl fl (App_stm B e1 e2)

| valid_let_rec : forall A vl fl B nf nx e1 e2,
    @rml_valid_type A vl ((nx,B) :: (nf,prod_choiceType B A) :: fl) e1 ->
    @rml_valid_type B vl fl e2 ->
    rml_valid_type A vl fl (Let_rec B A nf nx e1 e2)

| valid_random : forall vl fl e,
    rml_valid_type nat_choiceType vl fl e ->
    rml_valid_type nat_choiceType vl fl (Random e)

| valid_flip : forall vl fl,
    rml_valid_type bool_choiceType vl fl Flip.

Lemma dec_eq : (forall x y : choiceType, {x = y} + {x <> y}).
Proof.
  (* decide equality. *)
Admitted.

Fixpoint check_valid (A : choiceType) (vl : seq (nat * choiceType)) (fl : seq (nat * choiceType)) (x : Rml) {struct x} : bool :=
  match x with
  | Var p true => List.existsb (fun (a : nat * choiceType) => (p.1 == a.1) && asbool (p.2 = a.2)) fl && asbool (p.2 = A)
  | Var p false => List.existsb (fun (a : nat * choiceType) => (p.1 == a.1) && asbool (p.2 = a.2)) vl && asbool (p.2 = A)
  | Const A0 a => asbool (A = A0)
  | Let_stm p x1 x2 => check_valid p.2 vl fl x1 && check_valid A (p :: vl) fl x2
  | If_stm b m1 m2 => check_valid bool_choiceType vl fl b && check_valid A vl fl m1 && check_valid A vl fl m2
  | App_stm T e1 e2 => check_valid (prod_choiceType T A) vl fl e1 && check_valid T vl fl e2
  | Let_rec T T0 nf nx e1 e2 => check_valid A vl [:: (nx, T), (nf, prod_choiceType T T0) & fl] e1 && check_valid T vl fl e2 && asbool (T0 = A)
  | Random x => check_valid nat_choiceType vl fl x && asbool (nat_choiceType = A)
  | Flip => asbool (bool_choiceType = A)
  end.

Theorem type_checker :
  forall A vl fl x, check_valid A vl fl x = true <-> rml_valid_type A vl fl x.
Proof.
  assert (asbool_true : forall (k : choiceType), `[< k = k >] = true) by (intros ; apply (@asbool_equiv_eqP (k = k) true true) ; constructor ; easy ; easy).
  
  intros.
  split.
  { intros.
    generalize dependent fl.
    generalize dependent vl.
    generalize dependent A.
    induction x ; intros.
    { destruct b.
      {
        inversion H.
        rewrite H1.
        
        apply andb_prop in H1.
        inversion_clear H1.
        
        apply List.existsb_exists in H0.
        destruct H0.

        inversion_clear H0.
        
        apply andb_prop in H3.
        inversion_clear H3.

        apply asboolW in H2.
        apply asboolW in H4.

        apply PeanoNat.Nat.eqb_eq in H0.        
        subst.
        rewrite (surjective_pairing p).
        rewrite H0.
        rewrite H4.
        rewrite <- (surjective_pairing x).
        apply (valid_fun_var vl fl x).
        assumption.
      }
      {
        inversion H.

        apply andb_prop in H1.
        inversion_clear H1.

        apply List.existsb_exists in H0.
        destruct H0.
        
        inversion_clear H0.

        apply andb_prop in H3.
        inversion_clear H3.

        apply asboolW in H2.
        apply asboolW in H4.

        apply PeanoNat.Nat.eqb_eq in H0.

        rewrite (surjective_pairing p).
        rewrite H0.
        rewrite H4.
        rewrite <- (surjective_pairing x).

        subst.
        rewrite H4.

        apply (valid_var vl fl x).
        assumption.
      }  
    }
    {
      inversion H.
      apply asboolW in H1.
      subst.
      constructor.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply IHx1 in H0.
      apply IHx2 in H2.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply andb_prop in H0.
      inversion_clear H0.
      apply IHx1 in H1.
      apply IHx2 in H3.
      apply IHx3 in H2.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply IHx1 in H0.
      apply IHx2 in H2.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply andb_prop in H0.
      inversion_clear H0.
      apply asboolW in H2.
      apply IHx1 in H1.
      apply IHx2 in H3.
      subst.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply asboolW in H2.
      apply IHx in H0.
      subst.
      constructor ; assumption.
    }
    {
      inversion H.
      apply asboolW in H1.
      subst.
      constructor.
    }
  }
  {
    intros.
    generalize dependent fl.
    generalize dependent vl.
    generalize dependent A.
    induction x ; intros.
    {
      inversion H ; subst.
      {
        simpl.
        apply andb_true_intro.
        split.
        
        apply List.existsb_exists.
        exists p.
        split.

        assumption.

        apply andb_true_intro.
        split.
          
        apply eq_refl.
        apply (asbool_true p.2).

        apply (asbool_true p.2).
      }
      {
        simpl.
        apply andb_true_intro.
        split.
        
        apply List.existsb_exists.
        exists p.
        split.

        assumption.
        apply andb_true_intro.
          
        split.
        apply eq_refl.
        apply (asbool_true p.2).
        
        apply (asbool_true p.2).
      }
    }
    {
      inversion H ; subst.
      simpl.
      apply (asbool_true A).
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply IHx1.
      assumption.
      apply IHx2.
      assumption.
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply andb_true_intro.
      split.

      apply IHx1.
      assumption.
      apply IHx2.
      assumption.
      apply IHx3.
      assumption.
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply IHx1.
      assumption.
      apply IHx2.
      assumption.
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply andb_true_intro.
      split.

      apply IHx1 ; assumption.
      apply IHx2 ; assumption.
      apply (asbool_true t0).
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.
      
      apply IHx ; assumption.
      apply (asbool_true nat_choiceType).
    }
    {
      inversion H ; subst.
      simpl.
      apply (asbool_true bool_choiceType).
    }
  }
Defined.

(* -------------------------------------------------------------------------------- *)

Definition p_in_list (p : nat*Type) (l : seq (nat * Type)) : bool.
Proof.
  induction l.
  - refine false.
  - refine (if (asbool (a = p))
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
  - simpl in *.
    destruct `[< a = p >] eqn : eq.
    left.
    destruct eq.
    apply asboolW in H.
    assumption.
    right.
    apply IHl.
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

Inductive sRml {A : choiceType} :=
| sVar : nat -> sRml
| sConst : A -> sRml
| sIf : @sRml bool_choiceType -> sRml -> sRml -> sRml
| sApp : forall T, @sRml (prod_choiceType T A) -> @sRml T -> sRml
| sFix : forall B (nf nx : nat), @sRml A -> @sRml B -> sRml
| sRandom : (A = nat_choiceType) -> @sRml nat_choiceType -> sRml
| sFlip : (A = bool_choiceType) -> sRml.

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple {l : seq (nat * choiceType)} : Rml -> Prop :=
| is_fun_var : forall (p : nat * choiceType),
    List.In p l -> rml_is_simple (Var p true)
                                                             
| is_const : forall (A : choiceType) c,
    rml_is_simple (@Const A c)
                                           
| is_if : forall b m1 m2,
    rml_is_simple b ->
    rml_is_simple m1 ->
    rml_is_simple m2 ->
    rml_is_simple (@If_stm b m1 m2)
                  
| is_app : forall (B : choiceType) e1 e2,
    rml_is_simple e1 ->
    rml_is_simple e2 ->
    rml_is_simple (@App_stm B e1 e2)
                  
| is_fix : forall B C nf nx e1 e2,
    @rml_is_simple [:: (nx,B), (nf,prod_choiceType B C) & l] e1 ->
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

Inductive srml_valid_type (A : choiceType) : seq (nat * choiceType) -> @sRml A -> Prop :=
| svalid_fun_var : forall fl x,
    List.In (x,A) fl ->
    srml_valid_type A fl (sVar x)
                   
| svalid_const : forall fl (c : A),
    srml_valid_type A fl (sConst c)
                   
| svalid_if : forall fl b m1 m2,
    srml_valid_type bool_choiceType fl b ->
    srml_valid_type A fl m1 ->
    srml_valid_type A fl m2 ->
    srml_valid_type A fl (sIf b m1 m2)
                    
| svalid_app : forall fl (B : choiceType) e1 e2,
    @srml_valid_type (prod_choiceType B A) fl e1 ->
    @srml_valid_type B fl e2 ->
    @srml_valid_type A fl (sApp B e1 e2)
                     
| svalid_fix : forall fl B nf nx f x,
    @srml_valid_type A ((nx,B) :: (nf,prod_choiceType B A) :: fl) f ->
    @srml_valid_type B fl x ->
    srml_valid_type A fl (sFix B nf nx f x)

| svalid_random : forall fl e (H : A = nat_choiceType),
    srml_valid_type nat_choiceType fl e ->
    srml_valid_type A fl (sRandom H e)
                    
| svalid_flip : forall fl (H : A = bool_choiceType),
    srml_valid_type A fl (sFlip H).

(** * Properties of sRml expressions *)

(* -------------------------------------------------------------------------------- *)

Lemma helper :
  forall T A x1 x2 l, srml_valid_type A l (sApp T x1 x2) -> srml_valid_type (prod_choiceType T A) l x1 /\ srml_valid_type T l x2.
  intros.
  inversion H.

  assert (e3 = x2) by apply (inj_pair2_eq_dec choiceType dec_eq [eta @sRml] T e3 x2 H4).
  assert (e0 = x1) by apply (inj_pair2_eq_dec choiceType dec_eq (fun T : choiceType => @sRml _) T e0 x1 H1).
  subst ; clear H1 ; clear H4.  
  
  split ; assumption.
Qed.

Lemma helper2 :
  forall A B nx nf x1 x2 fl,
    srml_valid_type A fl (sFix B nf nx x1 x2) ->
    srml_valid_type A [:: (nx, B), (nf, prod_choiceType B A) & fl] x1 /\
    srml_valid_type B fl x2.
  intros.
  inversion H.
  subst.

  (* assert (f0 = x1) by (apply (inj_pair2_eq_dec Type dec_eq) in H4 ; assumption). *)
  assert (x0 = x2) by (apply (inj_pair2_eq_dec choiceType dec_eq) in H6 ; assumption).
  
  subst.
  
  split ; assumption.
Qed.

Lemma srml_valid_weakening:
  forall (p : nat * choiceType) (x : @sRml p.2) l1 l2 l3, srml_valid_type p.2 (l1 ++ l3) x -> srml_valid_type p.2 (l1 ++ l2 ++ l3) x.
Proof.
  intros.
  generalize dependent l1.
  induction x ; intros.
  - inversion H.
    constructor.
    apply List.in_app_or in H2.
    inversion H2.
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
    constructor ; eauto.
  - apply helper in H.
    inversion_clear H.
    + constructor ; eauto.
  - apply helper2 in H.
    inversion_clear H.
    constructor.
    + apply (IHx1 ([:: (nx, B), (nf, prod_choiceType B A) & l1])).
      assumption.
    + apply IHx2.
      assumption.
  - inversion_clear H.
    constructor ; eauto.
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
    inversion x_valid ; subst.
    apply (valid_fun_var vl fl (n,A)).
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
    constructor ; assumption.
  }

  (* sRandom *)
  {
    inversion_clear x_valid.

    subst.
    
    simpl.
    constructor.
    apply IHx.

    assumption.
  }

  (* sFlip *)
  {
    simpl.
    subst.
    constructor.
  }
Qed.

(** * Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * choiceType * Rml) -> seq (nat * choiceType) -> Prop :=
| env_nil l : valid_env nil l
| env_cons (x : nat * choiceType * Rml) xs l :
    (@rml_is_simple l x.2) ->
    (@rml_valid_type x.1.2 (map fst xs) l x.2) ->
    valid_env xs l ->
    valid_env (x :: xs) l.
                
Lemma valid_weakening:
  forall (a : nat * choiceType * Rml) l1 l2 l3 fl, rml_valid_type a.1.2 (l1 ++ l3) fl a.2 -> rml_valid_type a.1.2 (l1 ++ l2 ++ l3) fl a.2.
Proof.
  intros.
  destruct a.
  destruct p.
  simpl in *.
  generalize dependent fl.
  generalize dependent t.
  generalize dependent l1.
  induction r ; intros.
  (* Var *)
  {
    inversion H ; subst.
    + constructor.
      apply List.in_app_or in H4.
      inversion H4.
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
    * apply (IHr2 (p :: l1)).
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
    apply IHr.
    assumption.
  }

  (* Flip *)
  {
    inversion H ; subst.
    constructor.
  }
Qed.

Corollary valid_weakening_nil :
  forall (a : nat * choiceType * Rml) l1 l2 fl, rml_valid_type a.1.2 (l1) fl a.2 -> rml_valid_type a.1.2 (l1 ++ l2) fl a.2.
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
  forall (a : nat * choiceType * Rml) l1 l2 l3 vl, rml_valid_type a.1.2 vl (l1 ++ l3) a.2 -> rml_valid_type a.1.2 vl (l1 ++ l2 ++ l3) a.2.
Proof.
  intros.
  destruct a.
  destruct p.
  simpl in *.
  generalize dependent vl.
  generalize dependent t.
  generalize dependent l1.
  induction r ; intros.
  (* Var *)
  {
    inversion H ; subst.
    + constructor.
      assumption.
    + constructor.
      apply List.in_app_or in H4.
      inversion H4.
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
    apply (IHr1 [:: (n1,t) , (n0,prod_choiceType t t0) & l1]).
    assumption.
  }

  (* Random *)
  {
    inversion H ; subst.
    constructor.
    apply IHr.
    assumption.
  }

  (* Flip *)
  {
    inversion H ; subst.
    constructor.
  }
Qed.

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml_l {A : choiceType} (x : Rml) vl fl
         `{rml_simple : @rml_is_simple fl x} `{rml_valid : @rml_valid_type A vl fl x}
         {struct x} : exists (y : @sRml A), srml_valid_type A fl y.
Proof.
  (** Structure **)
  destruct x.

  (** Var **)
  {
    destruct b.
    - exists (sVar p.1).
      constructor.
      inversion rml_valid ; subst.
      rewrite <- surjective_pairing.
      assumption.
    - exfalso.
      inversion rml_simple.
  }
  
  (** Const **)
  {
    assert (A = A0) by (inversion rml_valid ; reflexivity) ; subst.
    exists (sConst s).
    constructor.
  }

  (** Let **)
  { exfalso ; easy. }

  (** If *)
  {
    assert (if_valid_type : (rml_valid_type bool_choiceType vl fl x1 /\ rml_valid_type A vl fl x2 /\ rml_valid_type A vl fl x3)) by (intros; inversion rml_valid; easy).
    inversion if_valid_type as [p1 [p2 p3]] ; clear if_valid_type.

    assert (if_is_simple : @rml_is_simple fl x1 /\ @rml_is_simple fl x2 /\ @rml_is_simple fl x3) by (inversion rml_simple ; subst ; easy).        
    inversion if_is_simple as [s1 [s2 s3]] ; clear if_is_simple.

    pose (rec1 := @rml_to_sRml_l bool_choiceType x1 vl fl s1 p1).
    pose (rec2 := @rml_to_sRml_l A x2 vl fl s2 p2).
    pose (rec3 := @rml_to_sRml_l A x3 vl fl s3 p3).

    destruct rec1 as [b'].
    destruct rec2 as [m1'].
    destruct rec3 as [m2'].
    
    exists (sIf b' m1' m2').
    constructor ; assumption.
  }

  (** App *)
  {    
    assert (app_valid_type : rml_valid_type (prod_choiceType t A) vl fl x1 /\ rml_valid_type t vl fl x2) by (inversion rml_valid ; subst ; split ; try constructor ; easy).
    
    inversion app_valid_type as [p1 p2] ; clear app_valid_type.

    assert (app_is_simple : @rml_is_simple fl x1 /\ @rml_is_simple fl x2) by (inversion rml_simple ; subst ; split ; try easy ; constructor ; assumption).
    
    inversion app_is_simple as [H1 H2] ; clear app_is_simple.

    pose (rec1 := @rml_to_sRml_l (prod_choiceType t A) x1 vl fl H1 p1).
    pose (rec2 := @rml_to_sRml_l t x2 vl fl H2 p2).

    destruct rec1 as [e1'].
    destruct rec2 as [e2'].
    
    exists (sApp t e1' e2').
    constructor ; assumption.
  }

  (** Let rec **)
  {
    
    assert (@rml_is_simple [:: (n0,t) , (n,prod_choiceType t t0) & fl] x1 /\ @rml_is_simple fl x2) by (inversion rml_simple ; subst ; easy).
        
    inversion_clear H.
    
    assert (rml_valid_type t0 vl [:: (n0,t), (n,prod_choiceType t t0) & fl] x1 /\ rml_valid_type t vl fl x2) by (inversion rml_valid ; inversion H8 ; subst ; easy).

    inversion_clear H.
    
    pose (rml_to_sRml_l t0 x1 vl ((n0,t) :: (n,prod_choiceType t t0) :: fl) H0 H2).
    pose (rml_to_sRml_l t x2 vl fl H1 H3).

    destruct e as [s].
    destruct e0 as [s0].
    
    assert (A = t0) by (inversion rml_valid ; reflexivity) ; subst.
    
    exists (sFix t n n0 s s0).
    constructor ; assumption.
  }

  (** Random **)
  {
    assert (@rml_is_simple fl x) by (inversion rml_simple ; assumption).
    assert (rml_valid_type nat_choiceType vl fl x) by (inversion rml_valid ; assumption).
    assert (A = nat_choiceType) by (inversion rml_valid ; reflexivity).
    
    pose (rml_to_sRml_l nat_choiceType x vl fl H H0).
    destruct e as [s].
    
    exists (sRandom H1 s).
    constructor ; assumption.
  }

  (** Flip **)
  {
    assert (A = bool_choiceType) by (inversion rml_valid ; reflexivity).
    exists (sFlip H).
    constructor.
  }
Defined.
  
(* -------------------------------------------------------------------------------- *)

Fixpoint lookup (p : (nat * choiceType)) (env : seq (nat * choiceType * Rml))
         (fl : seq (nat * choiceType))
         `{env_valid : valid_env env fl} `{_ : List.In p (map fst env) \/ List.In p fl}
         {struct env} : exists (y : @sRml p.2), srml_valid_type p.2 fl y.
  intros.
  induction env.
  - exists (sVar p.1).
    constructor.
    rewrite <- surjective_pairing.
    inversion H ; easy.
  - destruct (asbool (a.1 = p)) eqn : bo.
    + assert (@rml_is_simple fl a.2) by (inversion env_valid ; subst ; assumption).
      assert (rml_valid_type a.1.2 (map fst env) fl a.2) by (inversion env_valid ; assumption).
      apply asboolW in bo.
      subst.
      refine (@rml_to_sRml_l a.1.2 a.2 (map fst env) fl H0 H1).
    + apply IHenv.
      inversion env_valid ; assumption.
      inversion H.
      left.
      inversion H0.
      rewrite asboolT in bo.
      inversion bo.
      assumption.
      assumption.
      right.
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
    - apply (IHx1 ((n0,t) :: (n,prod_choiceType t t0) :: l1) l2 l3).
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

Fixpoint count_let (x : Rml) : nat :=
  match x with
  | Var _ _ | @Const _ _ | Flip => 0
  | Let_stm _ a b => 1 + count_let a + count_let b
  | If_stm a b c => count_let a + count_let b + count_let c
  | App_stm _ a b => count_let a + count_let b
  | Let_rec _ _ _ _ a b => count_let a + count_let b
  | Random a => count_let a
  end.

Fixpoint replace_all_variables_aux_type
         A (x : Rml) (env : seq (nat * choiceType * Rml))
         (fl : seq (nat * choiceType)) `{env_valid : valid_env env fl}
         `{x_valid : @rml_valid_type A (map fst env) fl x} {struct x} : exists (k : @sRml A), srml_valid_type A fl k.
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
    assert (A = t) by (inversion x_valid ; subst ; reflexivity) ; subst.
    apply (@lookup (n,t) env fl env_valid H).
  }

  (** Const **)
  {
    assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    exists (sConst s).
    constructor.
  }
      
  (** Let-stm **)
  {
    assert (x1_valid : rml_valid_type p.2 (map fst env) fl x1) by (inversion x_valid ; subst ; assumption).

    pose (x1' := replace_all_variables_aux_type p.2 x1 env fl env_valid x1_valid).
    destruct x1' as [x1'].
    pose (x1'' := @sRml_to_rml p.2 x1').

    assert (x1''_simple : @rml_is_simple fl x1'').
    apply sRml_simple.
    assumption.

    assert (x1''_valid : @rml_valid_type p.2 (map fst env) fl x1'').
    apply sRml_valid.
    assumption.
    
    pose (@rml_to_sRml_l p.2 x1'' (map fst env) fl).
        
    assert (x2_valid : rml_valid_type A (p :: [seq i.1 | i <- env]) fl x2) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((p,x1'') :: env) fl) by (constructor ; assumption).
    
    refine (replace_all_variables_aux_type A x2 ((p,x1'') :: env) fl env_valid' x2_valid).
  }
    
  (** If-stm **)
  {
    assert (x1_valid : rml_valid_type bool_choiceType (map fst env) fl x1) by (inversion x_valid ; subst ; assumption).
    assert (x2_valid : rml_valid_type A (map fst env) fl x2) by (inversion x_valid ; subst ; assumption).
    assert (x3_valid : rml_valid_type A (map fst env) fl x3) by (inversion x_valid ; subst ; assumption).
    
    pose (b' := replace_all_variables_aux_type bool_choiceType x1 env fl env_valid x1_valid).
    pose (m1' := replace_all_variables_aux_type A x2 env fl env_valid x2_valid).
    pose (m2' := replace_all_variables_aux_type A x3 env fl env_valid x3_valid).

    destruct b' as [b'].
    destruct m1' as [m1'].
    destruct m2' as [m2'].
    
    pose (b'' := sRml_to_rml b').
    pose (m1'' := sRml_to_rml m1').
    pose (m2'' := sRml_to_rml m2').
    
    refine (rml_to_sRml_l (If_stm b'' m1'' m2'') [seq i.1 | i <- env] fl).
    constructor ; eauto using sRml_simple.
    constructor ; eauto using sRml_valid.
  }

  (** App-stm **)
  {
    assert (x1_valid : rml_valid_type (prod_choiceType t A) (map fst env) fl x1) by (inversion x_valid ; subst ; assumption).
        
    assert (x2_valid : rml_valid_type t (map fst env) fl x2) by (inversion x_valid ; subst ; assumption).
    
    pose (e1' := replace_all_variables_aux_type (prod_choiceType t A) x1 env fl env_valid x1_valid).
    pose (e2' := replace_all_variables_aux_type t x2 env fl env_valid x2_valid).

    destruct e1' as [e1'].
    destruct e2' as [e2'].
    
    pose (e1'' := sRml_to_rml e1').
    pose (e2'' := sRml_to_rml e2').
    
    refine (rml_to_sRml_l (App_stm t e1'' e2'') [seq i.1 | i <- env] fl).
    constructor ; eauto 2 using sRml_simple.
    constructor ; eauto 2 using sRml_valid.
  }

  (** Let rec **)
  {
    pose (fl_x1 := [:: (n0, t), (n, prod_choiceType t t0) & fl]).
    
    assert (x1_valid : rml_valid_type A [seq i.1 | i <- env] fl_x1 x1) by (inversion x_valid ; subst ; assumption).
    
    assert (x2_valid : rml_valid_type t [seq i.1 | i <- env] fl x2) by (inversion x_valid ; subst ; assumption).

    
    assert (env_valid_x1 : valid_env env fl_x1) by (repeat apply extend_fl_still_valid ; assumption).
    
    pose (x1' := replace_all_variables_aux_type A x1 env fl_x1 env_valid_x1 x1_valid).
    assert (env_valid_x2 : valid_env env fl) by (repeat apply extend_fl_still_valid ; assumption).
    
    pose (x2' := replace_all_variables_aux_type t x2 env fl env_valid_x2 x2_valid).    

    destruct x1' as [x1'].
    destruct x2' as [x2'].
    
    assert (A = t0) by (inversion x_valid ; subst ; reflexivity) ; subst.
    
    exists (sFix t n n0 x1' x2').
    constructor ; assumption.        
  }

  (** Random **)
  {
    assert (rml_valid_type nat_choiceType (map fst env) fl x) by (inversion x_valid ; assumption).

    pose (replace_all_variables_aux_type nat_choiceType x env fl env_valid H).

    assert (A = nat_choiceType) by (inversion x_valid ; reflexivity).

    destruct e as [s].
    
    exists (sRandom H0 s).
    constructor ; assumption.
  }

  (** Flip **)
  {
    assert (A = bool_choiceType) by (inversion x_valid ; reflexivity).
    exists (sFlip H).
    constructor.
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