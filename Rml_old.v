From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.reals.

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
    unit := fun {A} (x : A) (f : A -> ZO) => f x ;
    bind := fun {A B} (mu : (A -> ZO) -> ZO) (M : A -> (B -> ZO) -> ZO) (f : B -> ZO) => mu (fun (x : A) => M x f)
  }. 
Proof. all: reflexivity. Defined.

(* -------------------------------------------------------------------------------- *)

Inductive Rml : Type :=
| Var : nat -> Rml
| Const : forall (A : Type), A -> Rml
| Let_stm : nat -> Rml -> Rml -> Rml
(* | Fun_stm : forall B, nat -> B -> @Rml A -> @Rml A *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed : seq nat -> Rml -> Prop :=
| well_const : forall A c l, well_formed l (Const A c)
| well_var : forall x l, List.In x l -> well_formed l (Var x)
| well_let_stm : forall x e1 e2 l, well_formed l e1 -> well_formed (x :: l) e2 -> well_formed l (Let_stm x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

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
  clear H4.
  inversion H6 ; subst ; clear H6.
  inversion H2.
  easy.
  easy.
Qed.  

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

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

Fixpoint replace_var_with_value (x : Rml) (index : nat) (value : Rml) : Rml :=
  match x with
  | Var n =>
    if n == index
    then value
    else x
  | Const A c => x
  | Let_stm n a b =>
    let new_value := replace_var_with_value a index value in
    if n == index
    then replace_var_with_value b index new_value
    else Let_stm n new_value (replace_var_with_value b index value)
  | If_stm b m1 m2 =>
    let b' := replace_var_with_value b index value in
    let m1' := replace_var_with_value m1 index value in
    let m2' := replace_var_with_value m2 index value in
    If_stm b' m1' m2'
  | App_stm B e1 e2 =>
    let e1' := replace_var_with_value e1 index value in
    let e2' := replace_var_with_value e2 index value in
    App_stm B e1' e2'
  end.

(* TODO: Make proof for correctness these two definitions *)

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
    assert (b_well : well_formed (n :: l) r2) by (inversion x_well ; subst ; assumption).
    
    refine (let a' := replace_var_for_let_aux r1 l a_well in
            let b' := replace_var_for_let_aux r2 (n :: l) b_well in
            replace_var_with_value b' n a').
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

Definition replace_var_for_let (x : Rml) `{x_well : well_formed nil x} : Rml :=
  @replace_var_for_let_aux x nil x_well.

Check List.fold_left.

Check List.remove.

Fixpoint var_in_exp (e : Rml) : seq nat :=
  match e with
  | Var n => [:: n]
  | If_stm b m1 m2 => var_in_exp b ++ var_in_exp m1 ++ var_in_exp m2
  | App_stm _ e1 e2 => var_in_exp e1 ++ var_in_exp e2
  | Let_stm x a b => var_in_exp a ++ filter (fun y => negb (x == y)) (var_in_exp b)
  | _ => [::]
  end.

Theorem helper :
  forall x l n,
    ~List.In n (var_in_exp x) -> well_formed l x -> well_formed (n :: l) x.
Proof.
  induction x ; intros ; simpl in *.
  + inversion H0 ; subst.
    induction l.
    * easy.
    * inversion H0 ; subst.
      simpl in H.
      intuition.
      apply well_var.
      apply List.in_cons.
      assumption.      
  + apply well_const.
  + apply well_let_stm.
    * apply IHx1.
      -- inversion H0 ; subst.
         simpl in H.
         intuition.
        -- inversion H0 ; subst.
           easy.
    * apply IHx2.
      induction (var_in_exp x2) eqn : varx2o.
      -- easy.
      -- simpl.
         unfold not.
         intros.
         inversion H1 ; clear H1.
         ++ subst.
            intuition.

            apply IHl0.
            
            
            apply H.

            simpl.
            apply List.in_app_iff.
            assert (forall (n : nat), (n != n) = false).
            --- intros.
                induction n1.
                +++ reflexivity.
                +++ apply IHn1.
            --- rewrite H1.
                
                

            
            inversion varx2o
            
            simpl.
            inversion H0 ; subst.

            apply H1.
               inversion H3.
               --- subst.
                   
                  apply List.in_cons in H3.
              apply H1.
            
        
      
      
      

Theorem helper :
  forall x1 x2 n l x1_well x2_well,
    ~List.In n (var_in_exp (@replace_var_for_let_aux x2 l x2_well))
    -> 
    (replace_var_with_value (@replace_var_for_let_aux x2 (n :: l) x2_well) n (@replace_var_for_let_aux x1 l x1_well)) = (replace_var_for_let_aux x2 l x2_well).
    

Theorem replace_vars_makes_simple :
  forall (x : Rml) (x_well : well_formed nil x), (var_in_exp (@replace_var_for_let x x_well)) = nil.
Proof.
  intros.
  destruct x.
  + inversion x_well ; subst.
    easy.
  + simpl.
    reflexivity.
  + inversion x_well ; subst.
    unfold replace_var_for_let.
    simpl.

    
            
    
    
    

(* Fixpoint replace_var_for_let (x : Rml) : Rml := *)
(*   match x with *)
(*   | Let_stm n a b => *)
(*     let b' := replace_var_for_let b in *)
(*     let a' := replace_var_for_let a in *)
(*     replace_var_with_value b' n a' *)
(*   | If_stm b m1 m2 => *)
(*     let b' := replace_var_for_let b in *)
(*     let m1' := replace_var_for_let m1 in *)
(*     let m2' := replace_var_for_let m2 in *)
(*       If_stm b' m1' m2' *)
(*   | App_stm B e1 e2 => *)
(*     let e1' := replace_var_for_let e1 in *)
(*     let e2' := replace_var_for_let e2 in *)
(*       App_stm B e1' e2' *)
(*   | _ => x *)
(*   end. *)

Definition example : Rml :=
  (If_stm (Const bool true)
          (Let_stm
             16 (Const bool true)
             (Let_stm
                12 (Const nat 4)
                (If_stm (Var 16) (Var 12) (Const nat 10))))
          (Const nat 900)).

Compute replace_var_with_value example 16 (Const bool true).
Compute replace_var_with_value example 12 (Const nat 4).   
Compute replace_var_for_let example.

(* -------------------------------------------------------------------------------- *)

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm B e1 e2).

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

Inductive rml_valid_type : Type -> Rml -> seq (nat * Type) -> Prop :=
| valid_var : forall x l A, List.In (x,A) l -> rml_valid_type A (Var x) l
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B} l, rml_valid_type A (Const B c) l
| valid_if : forall (A : Type) b m1 m2 l, rml_valid_type bool b l -> rml_valid_type A m1 l -> rml_valid_type A m2 l -> rml_valid_type A (If_stm b m1 m2) l
| valid_app : forall (A B : Type) e1 e2 l, rml_valid_type (B -> A) e1 l -> rml_valid_type B e2 l -> rml_valid_type A (App_stm B e1 e2) l
| valid_let : forall A B x a b l, rml_valid_type B a l -> rml_valid_type A b ((x,B) :: l) -> rml_valid_type A (Let_stm x a b) l.

(* -------------------------------------------------------------------------------- *)

Fixpoint rml_to_sRml {A : Type} (rml : Rml) `{rml_simple : rml_is_simple rml} `{rml_valid : rml_valid_type A rml nil} : @sRml A.
Proof.
  (* apply is_rml_simple_reflect_rml_is_simple in rml_simple. *)
  case rml eqn : o_rml.
  - exfalso.
    easy.
  - assert (forall (A B : Type) c l, rml_valid_type A (Const B c) l -> A = B) by (intros ; inversion H ; subst ; reflexivity).
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

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Definition valid_const' {A} c := @valid_const A A c (erefl A).
Definition is_const' {A} c := @is_const A c.

Definition rml_to_sRml_const {A} c := @rml_to_sRml A (Const A c) (is_const' c) (valid_const' c nil).

Compute interp_srml (rml_to_sRml_const 4).

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

Lemma replace_let_helper_lemma_simple :
  forall v1 v2 n, rml_is_simple v1 -> rml_is_simple (replace_var_with_value v1 n v2).
Proof.
  induction v1 ; intros.
  - easy.
  - apply is_const.
  - easy.
  - simpl in *.    
    inversion H as [H1 | H2 | H3] ; subst ; clear H.
    
    apply is_if.
    + apply IHv1_1. assumption.
    + apply IHv1_2. assumption.
    + apply IHv1_3. assumption.
  - simpl in *.
    inversion H as [H1 | H2 | H3] ; subst ; clear H.

    apply is_app.
    + apply IHv1_1. assumption.
    + apply IHv1_2. assumption.
Qed.

Lemma not_or_is_not :
  forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  intros.
  intuition.
Qed.

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
    
(*     apply replace_let_helper_lemma_simple. *)
(*     inversion x_valid ; subst. *)
(*     inversion x_well ; subst. *)
    
(*     induction x2. *)
(*     1 : {  } *)
(*       assumption. *)
    
(*   - intros A x_valid x_well. *)

(*     simpl. *)
(*     inversion x_well ; subst. *)
(*     inversion x_valid ; subst. *)
    
(*     apply is_if. *)
(*     + apply (IHx1 bool). *)
(*       assumption. *)
(*     + apply (IHx2 A). *)
(*       assumption. *)
(*     + apply (IHx3 A). *)
(*       assumption. *)
(*   - intros A x_valid x_well. *)
(*     inversion x_valid ; subst. *)
(*     inversion x_well. *)
(*     inversion H ; subst. *)
(*     apply is_app. *)
(*     + apply (IHx1 (T -> A)). *)
(*       assumption. *)
(*     + apply (IHx2 T). *)
(*       assumption. *)
(* Qed. *)

(* -------------------------------------------------------------------------------- *)

(* Lemma replace_let_helper_lemma_valid : *)
(*   forall A a b c x, rml_valid_type A (replace_var_with_value a x (replace_var_with_value b x c)) [::] <-> rml_valid_type A (replace_var_with_value a x (replace_var_with_value b x c)) [::]. *)
(* Proof. *)
(* Admitted. *)

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


Theorem replace_var_for_let_valid :
  forall {A} (x : Rml) `{x_valid : rml_valid_type A x nil} `{x_well : well_formed nil x},
    rml_valid_type A (@replace_var_for_let x x_well) nil.
Proof.
  intros.
  pose (H := @replace_var_for_let_simple x A x_valid x_well).
  
  generalize dependent A.
  induction x ; intros.
  - easy.
  - easy.
  - simpl in *.
    inversion H.
    + inversion x_valid ; subst.
      inversion H7 ; subst.
      * inversion H0.
      
      simpl in *.
      
      
      
  inversion H.
  - inversion x_valid ; subst.
    + easy.
    + unfold replace_var_for_let in *.
      simpl in *.
      inversion H1.
      apply valid_const.
      reflexivity.
    + unfold replace_var_for_let in *.
      simpl in *.
      inversion H1.
    + unfold replace_var_for_let in *.
      simpl in *.
      inversion H1.
    + unfold replace_var_for_let in *.
      simpl in *.
      
      
    
        
    
           

    (* apply IHx_valid2. *)
Admitted.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x nil} `{x_well : well_formed nil x} : continuation_monad_type R A :=
  let y := replace_var_for_let x in
  let y_simple := @replace_var_for_let_simple x A x_valid x_well in
  let y_valid := @replace_var_for_let_valid x A x_valid x_well in
  (interp_srml (@rml_to_sRml A y y_simple y_valid)).

(* -------------------------------------------------------------------------------- *)
(** * Examples **)

Compute @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil) _.

Compute @interp_rml _ (Let_stm 12 (@Const nat 4) (Var 12)) nat (@valid_let nat nat 12 (@Const nat 4 (@erefl Type nat) nil) _.

| valid_let : forall A B x a b l, rml_valid_type A a l -> rml_valid_type B b ((x,B) :: l) -> rml_valid_type A (Let_stm x a b) l.

(* -------------------------------------------------------------------------------- *)

Compute @interp_rml _ (@Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat)) _.
