Inductive well_formed_empty : Rml -> Prop :=
| well : forall rml, well_formed nil rml -> well_formed_empty rml.

Example var_not_well_formed :
  forall n, well_formed_empty (Var n) -> False.
Proof.
  intros.
  inversion H ; subst ; clear H.
  inversion H0 ; subst.
  easy.
Qed.

Example var_in_let_well_formed :
  forall n rml, well_formed_empty rml -> well_formed_empty (Let_stm n rml (Var n)).
Proof.
  intros.
  apply well.
  apply well_let_stm.
  - inversion H ; subst ; clear H.
    apply H0.
  - apply well_var.
  - left.
    reflexivity.
Qed.  

Example var_not_in_let_well_formed :
  forall n1 n2 rml, n1 <> n2 -> well_formed_empty (Let_stm n1 rml (Var n2)) -> False.
Proof.
  intros.
  inversion H0 ; subst ; clear H0.
  inversion H1 ; subst ; clear H1.
  - clear H4.
    inversion H6 ; subst ; clear H6.
    inversion H2 ; easy.
Qed.  

(* -------------------------------------------------------------------------------- *)

Fixpoint var_in_exp (e : Rml) : seq nat :=
  match e with
  | Var _ n => [:: n]
  | Let_stm x a b => var_in_exp a ++ filter (fun y => negb (x == y)) (var_in_exp b)
  | If_stm b m1 m2 => var_in_exp b ++ var_in_exp m1 ++ var_in_exp m2
  | App_stm _ e1 e2 => var_in_exp e1 ++ var_in_exp e2
  | _ => [::]
  end.

Compute var_in_exp (Let_stm 10 (Const nat 4) (Var _ 10)).

Theorem well_formed_weakening :
  forall x n l, well_formed (n :: l) x -> n \in (var_in_exp x) = false -> well_formed l x.
Proof.
  induction x ; intros.
  - apply well_var.
    destruct (n == n0) eqn : n0n.
    apply nat_equal in n0n.
    subst.
    simpl.
Admitted.

(* -------------------------------------------------------------------------------- *)

Fixpoint is_rml_simple (x : Rml) : bool :=
  match x with
  | Var _ => false
  | Const _ _ => true
  | Let_stm n a b => false
  | If_stm b m1 m2 => is_rml_simple b && is_rml_simple m1 && is_rml_simple m2
  | App_stm B e1 e2 => is_rml_simple e1 && is_rml_simple e2
  end.

Lemma double_andb_true : forall {b1 b2}, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  destruct b1.
  - destruct b2 ; easy.
  - easy.
Qed.

Lemma triple_andb_true : forall {b1 b2 b3}, b1 && b2 && b3 = true <-> b1 = true /\ b2 = true /\ b3 = true.
Proof.
  destruct b1.
  - destruct b2.
    + destruct b3 ; easy.
    + easy.
  - easy.
Qed.
  
Theorem is_rml_simple_reflect_rml_is_simple :
  forall (x : Rml),
    is_rml_simple x = true <-> rml_is_simple x.
Proof.
  induction x.
  - simpl.
    easy.
  - simpl.
    split.
    + intros.
      apply is_const.
    + easy.
  - simpl.
    easy.
  - simpl.
    split.
    + intros.
      apply triple_andb_true in H.
      inversion H as [H1 [H2 H3]] ; clear H.
      apply is_if ; intuition.
    + intros.
      inversion H ; subst.
      intuition.
  - simpl.
    split.
    + intros.
      apply double_andb_true in H.
      inversion H ; clear H.
      apply is_app ; intuition.
    + intros.
      inversion H ; subst.
      intuition.
Qed.  

(* -------------------------------------------------------------------------------- *)

Fixpoint replace_var_with_value (x : Rml) (index : nat) (A : Type) (value : Rml) : Rml :=
  match x with
  | Var B n =>
    if n == index
    then value
    else x
  | Const A c => x
  | Let_stm n a b =>
    let new_value := replace_var_with_value a index A value in
    if n == index
    then replace_var_with_value b index A new_value
    else Let_stm n new_value (replace_var_with_value b index A value)
  | If_stm b m1 m2 =>
    let b' := replace_var_with_value b index A value in
    let m1' := replace_var_with_value m1 index A value in
    let m2' := replace_var_with_value m2 index A value in
    If_stm b' m1' m2'
  | App_stm B e1 e2 =>
    let e1' := replace_var_with_value e1 index A value in
    let e2' := replace_var_with_value e2 index A value in
    App_stm B e1' e2'
  end.

Theorem replace_var_with_value_correctness :
  forall x n y, replaced_var_in_rml n y x (replace_var_with_value x n A y).
Proof.
  induction x ; intros.
  - simpl.
    destruct (n == n0) eqn : n0n.
    + apply nat_equal in n0n ; subst.
      apply replaced_var_same.
    + apply replaced_var_diff.
      assumption.
  - simpl.
    apply replaced_const.
  - simpl.
    destruct (n == n0) eqn : n0n.
    + apply nat_equal in n0n ; subst.
      apply (replaced_let_same n0 y x1 x2 (replace_var_with_value x1 n0 y)) ; easy.
    + apply replaced_let_diff ; easy.
  - apply replace_if ; easy.
  - apply replace_app ; easy.
Qed.      

Theorem replace_var_with_value_correctness :
  forall A x n y, replaced_var_in_rml n A y x (replace_var_with_value x n A y).
Proof.
  induction x ; intros.
  - simpl.
    destruct (n == n0) eqn : n0n.
    + apply nat_equal in n0n ; subst.
      apply replaced_var_same.
    + apply replaced_var_diff.
      assumption.
  - simpl.
    apply replaced_const.
  - simpl.
    destruct (n == n0) eqn : n0n.
    + apply nat_equal in n0n ; subst.
      apply (replaced_let_same n0 y x1 x2 (replace_var_with_value x1 n0 y)) ; easy.
    + apply replaced_let_diff ; easy.
  - apply replace_if ; easy.
  - apply replace_app ; easy.
Qed.      

Theorem replace_var_with_value_refl :
  forall x n y k, replaced_var_in_rml n y x k <-> replace_var_with_value x n y = k.
Proof.
  split ; intros.
  - induction H ; simpl ; try rewrite H ; try rewrite (nat_refl_equal n) ; try rewrite (nat_refl_equal n) ; subst ; try reflexivity.
    + 
  - subst.
    apply replace_var_with_value_correctness.
Qed.

(* -------------------------------------------------------------------------------- *)

Inductive rml_trans_correct {A} : Rml -> @sRml A -> Prop :=
| const : forall (c : A), rml_trans_correct (Const A c) (sConst c)
| ifstm : 
    forall rmlb (srmlb : @sRml bool), @rml_trans_correct bool rmlb srmlb ->
    forall rmlm1 (srmlm1 : @sRml A), rml_trans_correct rmlm1 srmlm1 ->
    forall rmlm2 (srmlm2 : @sRml A), rml_trans_correct rmlm2 srmlm2 ->
       rml_trans_correct (If_stm rmlb rmlm1 rmlm2) (sIf_stm srmlb srmlm1 srmlm2)
| appstm :
    forall (B : Type),
    forall rmle1 (srmle1 : @sRml (B -> A)), @rml_trans_correct (B -> A) rmle1 srmle1 ->
    forall rmle2 (srmle2 : @sRml B), @rml_trans_correct B rmle2 srmle2 ->
       rml_trans_correct (App_stm B rmle1 rmle2) (sApp_stm B srmle1 srmle2).

(* -------------------------------------------------------------------------------- *)

Theorem replace_vars_makes_simple_inductive_step :
  forall n1 n2 x (x_well : well_formed nil x) var2_well, var_in_exp (@replace_var_for_let x x_well) = nil -> var_in_exp (@replace_var_for_let (Let_stm n1 x (Var n2)) (well_let_stm n1 x (Var n2) nil x_well var2_well)) = nil.
Proof.
  intros.
  unfold replace_var_for_let in *.
  simpl.
  destruct (n2 == n1) eqn : nen.
  - apply nat_equal in nen.
    apply H.
  - inversion var2_well ; subst.
    inversion H2.
    + symmetry in H0.
      apply nat_equal in H0.
      rewrite H0 in nen.
      easy.
    + inversion H0.
Qed.

(* -------------------------------------------------------------------------------- *)

Lemma simple_let_if_simple_subexpressions :
  forall a x b,
    rml_is_simple b -> ~List.In x (var_in_exp b) -> rml_is_simple (replace_var_with_value b x a).
Proof.
  intros.
  induction b.
  - easy.
  - simpl.
    assumption.
  - easy.
  - simpl.
    inversion H ; subst.
    apply is_if.
    + apply IHb1.
      * assumption.
      * simpl in H0.
        intuition.
    + apply IHb2.
      * assumption.
      * simpl in H0.
        induction (var_in_exp b1).
        -- simpl in H0.
           intuition.
        -- apply IHl.
           ++ simpl in H0.
              intuition.
           ++ intros.
              intuition.
    + apply IHb3.
      * assumption.
      * simpl in H0.
        induction (var_in_exp b1).
        -- simpl in H0.
           intuition.
        -- apply IHl.
           ++ simpl in H0.
              intuition.
           ++ intros.
              intuition.
  - simpl.
    inversion H ; subst.
    apply is_app.
    + apply IHb1.
      * assumption.
      * simpl in H0.
        intuition.
    + apply IHb2.
      * assumption.
      * simpl in H0.
        intuition.
Qed.

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_for_let_simple :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x nil} `{x_well : well_formed nil x},
    rml_is_simple (@replace_var_for_let_aux x nil x_well).
Proof.  
  (* unfold replace_var_for_let. *)
  intros x.  
  induction x.
  - intros A x_valid x_well.
    simpl.
    inversion x_well ; subst.
    easy.        
    
  - intros B x_valid x_well.
    apply is_const.
  - intros A x_valid x_well.
    simpl.
    unfold replace_var_for_let.
    simpl.

    inversion x_valid ; subst.
    apply simple_let_if_simple_subexpressions.
Admitted.
    
Lemma replace_let_helper_lemma_valid :
  forall A B a b x l, rml_valid_type B a l -> rml_valid_type A b ((x,B) :: l) -> rml_valid_type A (replace_var_with_value b x a) l.
Proof.
Admitted.

Lemma replace_let_helper_lemma_valid2 :
  forall A B a b x l, (~List.In (x,B) l -> rml_valid_type A b l) -> rml_valid_type A (replace_var_with_value b x a) l.
Proof.
Admitted.

Lemma replace_let_helper_lemma_valid3 :
  forall b x l, ~List.In x l -> well_formed l b -> well_formed (x :: l) b.
Proof.
Admitted.

Lemma valid_weakening :
  forall A x n B l (_ : well_formed (map fst l) x), rml_valid_type A x ((n, B) :: l) -> rml_valid_type A x l.
Proof.
  intros.
Admitted.

(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall x A l `{x_valid : rml_valid_type A x l},
    well_formed (map fst l) x.
Proof.
  induction x ; intros.
  - apply well_var.
    inversion x_valid ; subst.
    induction l.
    + easy.
    + simpl.
      inversion H1.
      * left.
        rewrite H.
        simpl.
        reflexivity.
      * right.
        apply IHl.
        -- apply valid_var.
           assumption.
        -- assumption.
  - apply well_const.
  - inversion x_valid ; subst.
    apply well_let_stm.
    + apply (IHx1 B).
      assumption.
    + apply (IHx2 A ((n,B) :: l)).
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

Example correct_translation_const :
  forall A c, @rml_to_sRml A (@Const A c) (@is_const A c) (@valid_const A A c (erefl A) nil) = sConst c.
Proof. reflexivity. Qed.

Example correct_translation_if :
  forall A b n1 n2,
    let cb := (Const bool b) in
    let cn := (Const A n1) in
    let cns := (Const A n2) in
    @rml_to_sRml A
      (@If_stm cb cn cns)
      (@is_if cb cn cns (@is_const bool b) (@is_const A n1) (@is_const A n2))
      (@valid_if A cb cn cns nil (@valid_const bool bool b (@erefl Type bool) nil) (@valid_const A A n1 (erefl A) nil) (@valid_const A A n2 (erefl A) nil))
    = sIf_stm (sConst b) (sConst n1) (sConst n2).
Proof.  reflexivity. Qed.

Example correct_translation_app :
  forall (A B : Type) f x,
    let cf := (Const (A -> B) f) in
    let cx := (Const A x) in
    @rml_to_sRml B
      (@App_stm A cf cx)
      (@is_app A cf cx (@is_const (A -> B) f) (@is_const A x))
      (@valid_app B A cf cx nil (@valid_const (A -> B) (A -> B) f (erefl (A -> B)) nil) (@valid_const A A x (erefl A) nil))
    = sApp_stm A (sConst f) (sConst x).
Proof. reflexivity. Qed.
  
(* -------------------------------------------------------------------------------- *)

Definition valid_const' {A} c := @valid_const A A c (erefl A).
Definition is_const' {A} c := @is_const A c.

Definition rml_to_sRml_const {A} c := @rml_to_sRml A (Const A c) (is_const' c) (valid_const' c nil).

Compute interp_srml (rml_to_sRml_const 4).

(* -------------------------------------------------------------------------------- *)

Lemma not_or_is_not :
  forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  intros.
  intuition.
Qed.

(* -------------------------------------------------------------------------------- *)

Lemma replace_let_helper_lemma_simple :
  forall v1 v2 n, rml_is_simple v1 -> rml_is_simple (replace_var_with_value v1 n v2).
Proof.
  induction v1 ; intros.
  - easy.
  - apply is_const.
  - easy.
  - simpl in *.    
    inversion_clear H as [H1 | H2 | H3] ; subst.
    
    apply is_if.
    + apply IHv1_1. assumption.
    + apply IHv1_2. assumption.
    + apply IHv1_3. assumption.
  - simpl in *.
    inversion_clear H as [H1 | H2 | H3] ; subst.

    apply is_app.
    + apply IHv1_1. assumption.
    + apply IHv1_2. assumption.
Qed.

(* -------------------------------------------------------------------------------- *)

Example replace_is_success :
  forall A, replace_var_with_value (Let_stm (4,A) (Const nat 4) (Var (4,A))) (4,A) (Const nat 4) = (Const nat 4).
Proof.
  intros.
  simpl.
  destruct (pselect _).
  - simpl.
    reflexivity.
  - simpl.
    easy.
Qed.

Compute replace_var_with_value (Let_stm (4,_) (Const nat 4) (Var (4,_))) (4,_) (Const nat 4).

(* -------------------------------------------------------------------------------- *)

Lemma replace_var_with_value_type_correct :
  forall y x z n A l, replaced_var_in_rml l (n,A) y x z -> rml_valid_type A y l.
Proof.
  induction y ; intros.
  - destruct p.
    inversion H ; subst.
    
    pose (valid_var n0 l T).
    apply (valid_var n l A).

Qed.

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_for_with_value_valid :
  forall (x y : Rml) n {A} `{x_valid : rml_valid_type A x nil} {B} `{y_valid : rml_valid_type B y nil}, forall z, replaced_var_in_rml nil (n,A) y x z -> rml_valid_type A z nil.
Proof.
  induction x ; intros.
  - inversion x_valid ; subst.
    easy.
  - inversion x_valid ; subst.
    inversion H ; subst.
    apply valid_const.
    reflexivity.
  - inversion H ; subst.
    + inversion x_valid ; subst.
      apply valid_let with (B := B1).
      * pose (IHx1 y n B1 H6 B y_valid a').
Admitted.

(* -------------------------------------------------------------------------------- *)

Fixpoint replace_var_for_let_aux (x : Rml) {l} `{x_well : well_formed l x}: Rml.
  case x eqn : x_old.
  - (* Var *)
    intros.
    induction l.
    + easy.
    + refine x.
    
  - (* Const *)
    intros. refine x.
  - (* Let *)
    assert (a_well : well_formed l r1) by (inversion x_well ; subst ; assumption).
    assert (b_well : well_formed (p :: l) r2) by (inversion x_well ; subst ; assumption).
    
    refine (let a' := replace_var_for_let_aux r1 l a_well in
            let b' := replace_var_for_let_aux r2 (p :: l) b_well in
            replace_var_with_value b' p a').
  - (* If *)
    assert (b_well : well_formed l r1) by (inversion x_well ; subst ; assumption).
    assert (m1_well : well_formed l r2) by (inversion x_well ; subst ; assumption).
    assert (m2_well : well_formed l r3) by (inversion x_well ; subst ; assumption).

    refine (let b' := replace_var_for_let_aux r1 l b_well in
            let m1' := replace_var_for_let_aux r2 l m1_well in
            let m2' := replace_var_for_let_aux r3 l m2_well in
            If_stm b' m1' m2').
  - (* App *)
    assert (e1_well : well_formed l r1) by (inversion x_well ; subst ; assumption).
    assert (e2_well : well_formed l r2) by (inversion x_well ; subst ; assumption).

    refine (let e1' := replace_var_for_let_aux r1 l e1_well in
            let e2' := replace_var_for_let_aux r2 l e2_well  in
            App_stm T e1' e2').
Defined.
(* -------------------------------------------------------------------------------- *)

Lemma nat_S_equal :
  forall n x, (n.+1 == x.+1) = true <-> (n == x) = true.
Proof.
  induction n ; destruct x ; try easy ; try reflexivity.
Qed.

Lemma nat_equal :
  forall (n x : nat), n = x <-> (n == x) = true.
Proof.
  induction n ; destruct x ; try easy ; try reflexivity.
  split.
  - intros.
    inversion H.
    inversion H.
    apply nat_S_equal.
    apply (IHn x) in H1.
    rewrite H2 in H1.
    assumption.
  - intros.
    pose (nat_S_equal n x).
    symmetry in i.
    apply i in H.
    apply (IHn x) in H.
    rewrite H.
    reflexivity.
Qed.

Lemma nat_refl_equal :
  forall x : nat, (x == x) = true.
Proof.
  intros.
  pose (nat_equal x x).
  rewrite <- i.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------------- *)

Theorem replace_var_with_value_refl :
  forall A x n y k l, replaced_var_in_rml l (n,A) y x k <-> replace_var_with_value x (n,A) y = k.
Proof.
  split ; intros.
  - induction H ; simpl ; try rewrite H ; try rewrite (nat_refl_equal n) ; try rewrite (nat_refl_equal n) ; subst ; try reflexivity ; try destruct pselect ; easy.
  - subst.
    generalize dependent l.
    generalize dependent y.
    induction x ; intros.
    + simpl.
      destruct pselect ; simpl.
      * subst.
        apply replaced_var_same.
      * destruct p.
        apply replaced_var_diff.
        assumption.
    + simpl.
      apply replaced_const.
    + simpl.
      destruct pselect ; simpl.
      * subst.
        apply replaced_let_same with (a' := (replace_var_with_value x1 (n, A) y)).
        -- apply IHx1.
        -- apply IHx2.
      * destruct p.
        apply replaced_let_diff.
        -- assumption.
        -- apply IHx1.
        -- apply IHx2.
    + apply replaced_if ; easy.
    + apply replaced_app ; easy.
Qed.

Corollary replace_var_with_value_refl_nil :
  forall A x n y k, replaced_var_in_rml nil (n,A) y x k <-> replace_var_with_value x (n,A) y = k.
Proof. intros. apply replace_var_with_value_refl. Qed.

(* -------------------------------------------------------------------------------- *)

Inductive replaced_var_in_rml : seq (nat * Type) -> (nat * Type) -> Rml -> Rml -> Rml -> Prop :=
| replaced_var_diff : forall (n0 : nat) A, forall (n1 : nat) B, forall y l,
        (n0,A) <> (n1,B) ->
        replaced_var_in_rml l (n0,A) y (Var (n1,B)) (Var (n1,B))
                            
| replaced_var_same : forall l n A y,
    replaced_var_in_rml l (n,A) y (Var (n,A)) y
                        
| replaced_const : forall l n y, forall A c,
      replaced_var_in_rml l n y (Const A c) (Const A c)

| replaced_let_diff : forall l, forall n0 A, forall n1 B, forall y, forall a b a' b',
          (n0,A) <> (n1,B) ->
          replaced_var_in_rml l (n0,A) y a a' ->
          replaced_var_in_rml l (n0,A) y b b' ->
          replaced_var_in_rml l (n0,A) y (Let_stm (n1,B) a b) (Let_stm (n1,B) a' b')
                              
| replaced_let_same : forall l n A y, forall a b a' b',
      replaced_var_in_rml l (n,A) y a a' ->
      replaced_var_in_rml l (n,A) a' b b' ->
      replaced_var_in_rml l (n,A) y (Let_stm (n,A) a b) b'

| replaced_if : forall l n y, forall b m1 m2 b' m1' m2',
      replaced_var_in_rml l n y b b' ->
      replaced_var_in_rml l n y m1 m1' ->
      replaced_var_in_rml l n y m2 m2' ->
      replaced_var_in_rml l n y (If_stm b m1 m2) (If_stm b' m1' m2')

| replaced_app : forall l n y, forall B e1 e2 e1' e2',
      replaced_var_in_rml l n y e1 e1' ->
      replaced_var_in_rml l n y e2 e2' ->
      replaced_var_in_rml l n y (App_stm B e1 e2) (App_stm B e1' e2').

(* -------------------------------------------------------------------------------- *)

Compute (well_let_stm (10,_) (Const nat 4) (Var (10,_)) nil (well_const nat 4 nil) (well_var _ 10 [:: (10,_)] _)).

(* -------------------------------------------------------------------------------- *)

Check List.fold_left.

Check List.remove.

Definition type_nat : Type := nat.

Definition example : Rml :=
  (If_stm (Const bool true)
          (Let_stm
             (16,type_nat) (Const bool true)
             (Let_stm
                (12,type_nat) (Const nat 4)
                (If_stm (Var (16,type_nat)) (Var (12,type_nat)) (Const nat 10))))
          (Const nat 900)).

Compute replace_var_with_value example (16,type_nat) (Const bool true).
Compute replace_var_with_value example (12,type_nat) (Const nat 4).   
Compute replace_var_for_let example.

(* -------------------------------------------------------------------------------- *)

(** * Examples **)

Compute @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil). (* _ => bug *)

Compute @interp_rml _ (Let_stm (12,_) (@Const nat 4) (Var (12,_))) nat (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat _)).

Example const_4_interp :
  forall R Q, @interp_rml R (Let_stm (12,_) (@Const nat 4) (Var (12,_))) nat (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat Q)) = @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil).
Proof.
  simpl.
Admitted.