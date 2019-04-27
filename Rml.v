From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.

(* -------------------------------------------------------------------------------- *)

Inductive Rml :=
| Var : (nat * Type) -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : (nat * Type) -> Rml -> Rml -> Rml
| Fun_stm : Type -> (nat * Type) -> Rml -> Rml
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml
| Let_rec : Type -> Type -> nat -> nat -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed (vl : seq (nat * Type)) (fl : seq (nat * Type)) : Rml -> Prop :=
| well_var : forall A x,
    List.In (x,A) vl ->
    well_formed vl fl (Var (x,A))

| well_fun_var : forall A x,
    List.In (x,A) fl ->
    well_formed vl fl (Var (x,A))
                
| well_const : forall A c,
    well_formed vl fl (Const A c)
                
| well_let : forall x (e1 e2 : Rml),
    @well_formed vl fl e1 ->
    @well_formed (x :: vl) fl e2 ->
    well_formed vl fl (Let_stm x e1 e2)

| well_fun : forall C p x,
    @well_formed vl (p :: fl) x ->
    @well_formed vl fl (Fun_stm C p x)
                
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
    @well_formed vl ((nx,B) :: (nf,B -> C) :: fl) e1 ->
    @well_formed vl ((nf,B -> C) :: fl) e2 ->
    well_formed vl fl (Let_rec B C nf nx e1 e2)

| well_fun_app : forall C p x1 x2,
    well_formed vl (p :: fl) x1 ->
    well_formed vl fl x2 ->
    well_formed vl fl (App_stm p.2 (Fun_stm C p x1) x2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} :=
| sVar : nat -> sRml
| sConst : A -> sRml
| sFun : forall C (p : nat * Type), A = (p.2 -> C) -> @sRml C -> sRml
| sIf : @sRml bool -> sRml -> sRml -> sRml
| sApp : forall T, @sRml (T -> A) -> @sRml T -> sRml
| sFix : forall B (nf nx : nat), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type (A : Type) (vl : seq (nat * Type)) (fl : seq (nat * Type)) : Rml -> Prop :=
| valid_var : forall x,
    List.In (x,A) vl ->
    rml_valid_type A vl fl (Var (x,A))

| valid_fun_var : forall x,
    List.In (x,A) fl ->
    rml_valid_type A vl fl (Var (x,A))
                   
| valid_const : forall (c : A),
    rml_valid_type A vl fl (Const A c)
                   
| valid_let : forall B x a b,
    @rml_valid_type B vl fl a ->
    @rml_valid_type A ((x,B) :: vl) fl b ->
    rml_valid_type A vl fl (Let_stm (x,B) a b)

| valid_fun : forall C p x,
    (A = (p.2 -> C)) ->
    rml_valid_type C vl (p :: fl) x ->
    rml_valid_type A vl fl (Fun_stm C p x)
                   
| valid_if : forall b m1 m2,
    rml_valid_type bool vl fl b ->
    rml_valid_type A vl fl m1 ->
    rml_valid_type A vl fl m2 ->
    rml_valid_type A vl fl (If_stm b m1 m2)
                   
| valid_app : forall (B : Type) e1 e2,
    rml_valid_type (B -> A) vl fl e1 ->
    rml_valid_type B vl fl e2 ->
    rml_valid_type A vl fl (App_stm B e1 e2)

| valid_let_rec : forall B C nf nx e1 e2,
    @rml_valid_type (B -> C) vl ((nx,B) :: (nf,B -> C) :: fl) e1 ->
    (* ^ Should be ((B -> C) -> B -> C) *)
    @rml_valid_type A vl ((nf,B -> C) :: fl) e2 ->
    rml_valid_type A vl fl (Let_rec B C nf nx e1 e2)
                   
(* | valid_let_rec : forall B C f x a b, *)
(*     @rml_valid_type (B -> C) ((x,B) :: (f,B -> C) :: vl) fl a -> *)
(*     @rml_valid_type A ((f,B -> C) :: vl) fl b -> *)
(*     rml_valid_type A vl fl (Let_rec (f,B -> C) (x,B) a b) *)

| valid_fun_app : forall p x1 x2,
    rml_valid_type A vl (p :: fl) x1 ->
    rml_valid_type p.2 vl fl x2 ->
    rml_valid_type A vl fl (App_stm p.2 (Fun_stm A p x1) x2).

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

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple {l : seq (nat * Type)} : Rml -> Prop :=
| is_fun_var : forall (p : nat * Type), List.In p l -> rml_is_simple (Var p)
| is_const : forall (A : Type) c, rml_is_simple (@Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (@If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (@App_stm B e1 e2)
| is_fun_app : forall nx (B C : Type) e1 e2, @rml_is_simple ((nx,B) :: l) e1 -> rml_is_simple e2 -> rml_is_simple (@App_stm B (@Fun_stm C (nx,B) e1) e2)
| is_fun : forall C p x, @rml_is_simple (p :: l) x -> rml_is_simple (@Fun_stm C p x)
| is_fix : forall B C nf nx e1 e2, @rml_is_simple [:: (nx,B), (nf,B -> C) & l] e1 -> @rml_is_simple ((nf,B -> C) :: l) e2 -> rml_is_simple (@Let_rec B C nf nx e1 e2).

(* -------------------------------------------------------------------------------- *)

Fixpoint sRml_to_rml {A} (x : @sRml A) : Rml :=
  match x with
  | sVar n => Var (n,A)
  | sConst c => Const A c
  | sFun C p _ x => Fun_stm C p (sRml_to_rml x)
  | sIf b m1 m2 => If_stm (sRml_to_rml b) (sRml_to_rml m1) (sRml_to_rml m2)
  | sApp T e1 e2 => App_stm T (sRml_to_rml e1) (sRml_to_rml e2)
  | sFix B nf nx f x =>
    (Let_rec B A nf nx (sRml_to_rml f) (App_stm B (Var (nf,B -> A)) (sRml_to_rml x)))
                           (* TODO *)
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
    @srml_valid_type (B -> A) ((nx,B) :: (nf,B -> A) :: fl) f ->
    (* ^ Should be ((B -> C) -> B -> C) *)
    @srml_valid_type B ((nf,B -> A) :: fl) x ->
    srml_valid_type A fl (sFix B nf nx f x).

Lemma helper :
  forall T A x1 x2 l, srml_valid_type A l (sApp T x1 x2) -> srml_valid_type (T -> A) l x1 /\ srml_valid_type T l x2.
Admitted.

Lemma helper2 :
  forall A B nx nf x1 x2 fl,
    srml_valid_type A fl (sFix B nf nx x1 x2) ->
    srml_valid_type (B -> A) [:: (nx, B), (nf, B -> A) & fl] x1 /\ srml_valid_type B ((nf, B -> A) :: fl) x2.
Admitted.

Lemma srml_valid_weakening:
  forall (p : nat * Type) (x : @sRml p.2) l1 l2 l3, srml_valid_type p.2 (l1 ++ l3) x -> srml_valid_type p.2 (l1 ++ l2 ++ l3) x.
Proof.
Admitted.

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

  (* sFun *)
  { inversion x_valid. }

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
    inversion x_valid ; subst.
    apply helper2 in x_valid.
    inversion x_valid ; subst.
    simpl.
    constructor.
    - apply IHx1.
      assumption.
    - constructor.
      + constructor.
        left.
        reflexivity.
      + apply IHx2.
        assumption.
  }
Qed.

Lemma sRml_valid :
  forall A (x : @sRml A) vl fl (x_valid : srml_valid_type A fl x),
    rml_valid_type A vl fl (@sRml_to_rml A x).
Proof.
  induction x ; intros.
  - simpl.
    inversion x_valid.
    apply valid_fun_var.
    assumption.
  - constructor.
  - inversion x_valid.
  - simpl.
    inversion x_valid.
    constructor ; eauto.
  - simpl.
    apply helper in x_valid.
    inversion x_valid.
    constructor ; eauto.
  - simpl.    
    apply helper2 in x_valid.
    
    inversion x_valid ; subst.
    simpl.
    constructor.
    + apply IHx1.
      assumption.
    + constructor.
      * apply valid_fun_var.
        left.
        reflexivity.
      * apply IHx2.
        assumption.
Qed.

(** Environment **)
(* -------------------------------------------------------------------------------- *)

Inductive valid_env : seq (nat * Type * Rml) -> seq (nat * Type) -> Prop :=
| env_nil l : valid_env nil l
| env_cons (x : nat * Type * Rml) xs l :
    (@rml_is_simple l x.2) ->
    (@rml_valid_type x.1.2 (map fst xs) l x.2) ->
    valid_env xs l ->
    valid_env (x :: xs) l.

Lemma helper3 :
  forall A B C D,
    (A -> B) = (C -> D) -> A = C /\ B = D.
Admitted.

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
  - inversion H ; subst.
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
    + apply valid_fun_var.
      assumption.
    + inversion H ; subst.
      constructor.
    + inversion H ; subst.
      constructor.
      * apply IHr1.
        assumption.
      * apply (IHr2 ((x,B) :: l1)).
        assumption.
    + inversion H ; subst.
      simpl.
      apply IHr in H4.
      apply valid_fun ; easy.
    + inversion H ; subst.
      constructor ; eauto.
    + inversion H ; subst.
      * constructor ; eauto.
      * apply valid_fun_app.
        assert (rml_valid_type (p.2 -> T0) (l1 ++ l2 ++ l3) fl (Fun_stm T0 p x1)).
          by (apply IHr1 ; apply valid_fun ; try reflexivity ; assumption).
        inversion H0 ; subst.
        apply helper3 in H5.
        inversion H5 ; subst.
        assumption.
        eauto.        
    + inversion H ; subst.
      constructor ; eauto.
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
  - inversion H ; subst.
    + constructor.
      assumption.
    + apply valid_fun_var.
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
  - inversion H.
    constructor.
  - inversion H ; subst.
    constructor.
    + apply IHr1.
      assumption.
    + apply IHr2.
      assumption.
  - inversion H ; subst.
    apply valid_fun ; eauto.
    apply (IHr (p :: l1)).
    assumption.
  - inversion H ; subst.
    constructor ; eauto.
  - inversion H ; subst.
    + constructor ; eauto.
    + constructor.
      * apply IHr1.
        apply valid_fun ; easy.
      * eauto.      
  - inversion H ; subst.
    constructor.
    + apply (IHr1 [:: (n1,T) , (n0,T -> T0) & l1]).
      assumption.
    + apply (IHr2 [:: (n0,T -> T0) & l1]).
      assumption.
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

  (** Fun **)
  {
    assert (fun_valid_type : rml_valid_type T vl (p :: fl) r) by (inversion rml_valid ; subst ; assumption).

    assert (@rml_is_simple [:: p & fl] r) by (inversion rml_simple ; subst ; assumption).
    
    pose (rml_to_sRml_l T r vl (p :: fl) H fun_valid_type).

    assert (A = (p.2 -> T)) by (inversion rml_valid ; subst ; reflexivity).
    exact (sFun T p H0 s).
  }

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
  { assert (@rml_is_simple [:: (n0,T) , (n,T -> T0) & fl] r1 /\ @rml_is_simple ((n,T -> T0) :: fl) r2) by (inversion rml_simple ; subst ; easy).

    inversion_clear H.
    
    assert (rml_valid_type (T -> T0) vl [:: (n0,T), (n,T -> T0) & fl] r1 /\ rml_valid_type A vl ((n,T -> T0) :: fl) r2) by (inversion rml_valid ; subst ; easy).
    
    inversion_clear H.

    (* TODO WRITE THIS OUT ON PAPER *)
    
    pose (rml_to_sRml_l (T -> T0) r1 vl ((n0,T) :: (n,T -> T0) :: fl) H0 H2).
    pose (rml_to_sRml_l A r2 vl ((n,T -> T0) :: fl) H1 H3).

    assert (@rml_is_simple fl (Fun_stm A (n, T -> T0) r2)) by (constructor ; assumption).
    assert (rml_valid_type ((T -> T0) -> A) vl fl (Fun_stm A (n, T -> T0) r2)).
    constructor.
    reflexivity.
    assumption.

    (* Fun insert start *)

    assert (fun_valid_type : rml_valid_type A vl ((n,T -> T0) :: fl) r2) by (inversion H4 ; subst ; assumption).

    assert (@rml_is_simple [:: (n,T -> T0) & fl] r2) by (inversion rml_simple ; subst ; assumption).
    
    pose (rml_to_sRml_l A r2 vl ((n,T -> T0) :: fl) H5 fun_valid_type).

    assert (((n,T -> T0).2 -> A) = ((n,T -> T0).2 -> A)) by (inversion rml_valid ; subst ; reflexivity).
    pose (sFun A (n,T -> T0) H6 s1).

    (* Fun insert end *)
      
    (* pose (rml_to_sRml_l ((T -> T0) -> A) (Fun_stm A (n,T -> T0) r2) vl fl H H4). *)
    
    (* WORK TO DO HERE *)
    
    exact (@sFix A (T -> T0) n n0 s2 s).
  }
Defined.

(* -------------------------------------------------------------------------------- *)

Theorem srml_to_rml_correctness :
  forall A fl (srml : @sRml A) (valid : srml_valid_type A fl srml),
    srml = @rml_to_sRml_l A (@sRml_to_rml A srml) nil fl (@sRml_simple A srml fl valid) (sRml_valid A srml nil fl valid).
Proof.
  induction srml ; intros.
  - simpl.
    reflexivity.
  - inversion valid ; subst.
    
Admitted.

Theorem rml_to_srml_correctness :
  forall A rml vl fl simple valid,
     rml = @sRml_to_rml A (@rml_to_sRml_l A rml vl fl simple valid).
Proof.
  induction rml ; intros.
  - simpl.
    destruct p.
    inversion valid ; subst.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  -
Admitted.

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

Lemma valid_rml_makes_valid_srml :
  forall A x y vl fl, rml_valid_type A vl fl x -> srml_valid_type A fl y.
Proof.
Admitted.

(* Lemma valid_rml_makes_valid_srml : *)
(*   forall A x vl fl `{x_simple : @rml_is_simple fl x} (x_valid : rml_valid_type A vl fl x), srml_valid_type A fl (@rml_to_sRml_l A x vl fl x_simple x_valid). *)
(* Proof. *)
(*   intros. *)
(*   induction x. *)
(*   - destruct p. *)
(*     assert (A = T) by (inversion x_valid ; subst ; reflexivity) ; subst. *)
(*     inversion x_simple ; subst. *)
(*     constructor. *)
(*     assumption. *)
(*   -  *)
(* Admitted. *)

Lemma rml_simple_weakening :
  forall x l1 l2 l3, @rml_is_simple (l1 ++ l3) x -> @rml_is_simple (l1 ++ l2 ++ l3) x.
Proof.
  induction x ; intros.
  - constructor.
    inversion H.
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
  - inversion H.
  - inversion H ; subst.
    constructor.
    apply (IHx (p :: l1) l2 l3).
    assumption.
  - inversion H ; subst.
    constructor ; eauto.
  - inversion H ; subst.
    + constructor ; eauto.
    + constructor.
      * apply IHx1.
        constructor.
        assumption.
      * apply IHx2.
        assumption.
  - inversion H ; subst.
    constructor.
    + apply (IHx1 ((n0,T) :: (n,T -> T0) :: l1) l2 l3).
      assumption.
    + apply (IHx2 ((n,T -> T0) :: l1) l2 l3).
      assumption.
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
  {
    assert (List.In p (map fst env) \/ List.In p fl) by (inversion x_valid ; subst ; auto).
    destruct p.
    assert (A = T) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (@lookup (n,T) env fl env_valid H).
  }
  {
    assert (A0 = A) by (inversion x_valid ; subst ; reflexivity) ; subst.
    refine (sConst a).
  }
      
  (** Let-stm **)
  {
    assert (x1_valid : rml_valid_type p.2 [seq i.1 | i <- env] fl x1) by (inversion x_valid ; subst ; assumption).
    
    pose (x1' := replace_all_variables_aux_type p.2 x1 env fl env_valid x1_valid).
    
    pose (x1'' := sRml_to_rml x1').

    pose (x1'_valid := valid_rml_makes_valid_srml p.2 x1 x1' [seq i.1 | i <- env] fl x1_valid).
    
    pose (x1''_simple := @sRml_simple p.2 x1' fl x1'_valid).
    pose (x1''_valid := sRml_valid p.2 x1' [seq i.1 | i <- env] fl x1'_valid).

    assert (x2_valid : rml_valid_type A (p :: [seq i.1 | i <- env]) fl x2) by (inversion x_valid ; subst ; assumption).

    assert (env_valid' : valid_env ((p,x1'') :: env) fl) by (constructor ; assumption).
    
    refine (replace_all_variables_aux_type A x2 ((p,x1'') :: env) fl env_valid' x2_valid).
  }
  
  (** Fun-stm **)
  {
    assert (fun_valid : rml_valid_type T (map fst env) (p :: fl) x) by (inversion x_valid ; subst ; assumption).

    pose (fl_valid := extend_fl_still_valid p env fl env_valid).
    
    pose (x' := replace_all_variables_aux_type T x env (p :: fl) fl_valid fun_valid).

    assert (A = (p.2 -> T)) by (inversion x_valid ; subst ; reflexivity).

    refine (sFun T p H x').
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
    assert (x1_valid : rml_valid_type (T -> A) (map fst env) fl x1).
    - inversion x_valid ; subst.
      + assumption.
      + constructor.
        * reflexivity.
        * assumption.
        
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

  { (* n = f, n0 = x *)

    assert (rml_valid_type (T -> T0) [seq i.1 | i <- env] [:: (n0, T), (n, T -> T0) & fl] x1) by (inversion x_valid ; subst ; assumption).

    assert (env_valid_x1 : valid_env env [:: (n0, T), (n, T -> T0) & fl]) by (do 2 apply extend_fl_still_valid ; assumption).
    
    pose (replace_all_variables_aux_type (T -> T0) x1 env [:: (n0,T), (n,T -> T0) & fl] env_valid_x1 H).
      
    pose (@sFix T0 T n n0 s). (* To replace vars with in x2 *)

    assert ((T -> T0) = (T -> T0)) by reflexivity.
    pose (@sFun (T -> T0) T0 (n0,T) H0 (s0 (sVar n0))).

    assert (valid_env env ((n,T -> T0) :: fl)) by (apply extend_fl_still_valid ; assumption).
    assert (rml_valid_type A [seq i.1 | i <- env] ((n, T -> T0) :: fl) x2).
    inversion x_valid ; subst.
    assumption.

    assert (rml_valid_type ((T -> T0) -> A) [seq i.1 | i <- env] fl (Fun_stm A (n, T -> T0) x2)).
    constructor.
    simpl.
    reflexivity.
    inversion x_valid ; subst.
    assumption.

    (* Insert fun_stm here *)

    assert (fun_valid : rml_valid_type A (map fst env) ((n,T -> T0) :: fl) x2).
    inversion H3 ; subst ; assumption.

    pose (fl_valid := extend_fl_still_valid (n,T -> T0) env fl env_valid).
    
    pose (x' := replace_all_variables_aux_type A x2 env ((n,T -> T0) :: fl) fl_valid fun_valid).

    assert (((T -> T0) -> A) = ((n, T -> T0).2 -> A)) by reflexivity.
    pose (s2 := sFun A (n,T -> T0) H4 x').
    
    (* End of insert *)
    
    (* pose (replace_all_variables_aux_type ((T -> T0) -> A) (Fun_stm A (n,T -> T0) x2) env fl env_valid H3). *)
    
    pose (sApp (T -> T0) s2 s1).
    
    refine s3.
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
    - constructor.
      + eauto.
      + eauto.
    - apply well_fun_app.
      + assert (rml_valid_type (p.2 -> A) vl fl (Fun_stm A p x0)).
        constructor.
        reflexivity.
        assumption.
        apply IHx1 in H.
        inversion H ; subst.
        assumption.
      + apply (IHx2 p.2).
        assumption.
  }

  all: inversion x_valid ; subst ; try (apply well_fun_var ; assumption) ; try (constructor ; eauto).
Qed.

(* -------------------------------------------------------------------------------- *)
