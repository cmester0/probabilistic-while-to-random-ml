From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import analysis.reals.
From mathcomp.analysis Require Import boolp reals distr.
From Hammer Require Import Hammer.

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
| Let_stm : (nat * Type) -> Rml -> Rml -> Rml
(* | Fun_stm : forall B, (nat * Type) -> B -> Rml -> Rml *)
| If_stm : Rml -> Rml -> Rml -> Rml
| App_stm : Type -> Rml -> Rml -> Rml.

(* -------------------------------------------------------------------------------- *)

Inductive well_formed : seq (nat * Type) -> Rml -> Prop :=
| well_var : forall A x l, List.In (x,A) l -> well_formed l (Var (x,A))
| well_const : forall A c l, well_formed l (Const A c)
| well_let_stm : forall x e1 e2 l, well_formed l e1 -> well_formed (x :: l) e2 -> well_formed l (Let_stm x e1 e2)
| well_if : forall b m1 m2 l, well_formed l b -> well_formed l m1 -> well_formed l m2 -> well_formed l (If_stm b m1 m2)
| well_app : forall B e1 e2 l, well_formed l e1 -> well_formed l e2 -> well_formed l (App_stm B e1 e2).

(* -------------------------------------------------------------------------------- *)

Inductive sRml {A : Type} : Type :=
| sConst : A -> @sRml A
| sIf_stm : @sRml bool -> sRml -> sRml -> sRml
| sApp_stm : forall (B : Type), @sRml (B -> A) -> @sRml B -> sRml.

(* -------------------------------------------------------------------------------- *)

Fixpoint replace_var_with_value (x : Rml) (index : (nat * Type)) (value : Rml) : Rml :=
  match x with
  | Var n =>
    if pselect (index = n)
    then value
    else x
  | Const A c => x
  | Let_stm n a b =>
    let a' := replace_var_with_value a index value in
    let b'1 := replace_var_with_value b n a' in
    let b'2 :=  (replace_var_with_value b index value) in
    
    if pselect (index = n)
    then b'1
    else Let_stm n a' b'2
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

Fixpoint replace_var_for_let_aux (x : Rml) {l} : Rml :=
  match x with
  | Const _ _ | Var _ => x
  | Let_stm p r1 r2 =>
    let a' := @replace_var_for_let_aux r1 l in
    let b' := @replace_var_for_let_aux r2 (p :: l) in
    replace_var_with_value b' p a'
  | If_stm r1 r2 r3 =>
    let b' := @replace_var_for_let_aux r1 l in
    let m1' := @replace_var_for_let_aux r2 l in
    let m2' := @replace_var_for_let_aux r3 l in
    If_stm b' m1' m2'
  | App_stm T r1 r2 =>
    let e1' := @replace_var_for_let_aux r1 l in
    let e2' := @replace_var_for_let_aux r2 l in
    App_stm T e1' e2'
  end.

Definition replace_var_for_let (x : Rml) `{x_well : well_formed nil x} : Rml :=
  @replace_var_for_let_aux x nil.

(* -------------------------------------------------------------------------------- *)

Inductive rml_valid_type : Type -> Rml -> seq (nat * Type) -> Prop :=
| valid_var : forall x l A, List.In (x,A) l -> rml_valid_type A (Var (x,A)) l
| valid_const : forall (A B : Type) (c : B) {_ : @eq Type A B} l, rml_valid_type A (Const B c) l
| valid_let : forall A B x a b l, rml_valid_type B a l -> rml_valid_type A b ((x,B) :: l) -> rml_valid_type A (Let_stm (x,B) a b) l
| valid_if : forall (A : Type) b m1 m2 l, rml_valid_type bool b l -> rml_valid_type A m1 l -> rml_valid_type A m2 l -> rml_valid_type A (If_stm b m1 m2) l
| valid_app : forall (A B : Type) e1 e2 l, rml_valid_type (B -> A) e1 l -> rml_valid_type B e2 l -> rml_valid_type A (App_stm B e1 e2) l.
                                                                                            
(* -------------------------------------------------------------------------------- *)

Theorem valid_is_well :
  forall x A l `{x_valid : rml_valid_type A x l},
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

Inductive rml_is_simple : Rml -> Prop :=
| is_const : forall (A : Type) c, rml_is_simple (Const A c)
| is_if : forall b m1 m2, rml_is_simple b -> rml_is_simple m1 -> rml_is_simple m2 -> rml_is_simple (If_stm b m1 m2)
| is_app : forall (B : Type) e1 e2, rml_is_simple e1 -> rml_is_simple e2 -> rml_is_simple (App_stm B e1 e2).

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

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Lemma valid_var_nil_is_false :
  forall A p, ~ rml_valid_type A (Var p) nil.
Proof.
  intros.
  unfold not.
  intros.
  inversion H ; subst.
  contradiction.
Qed.

Lemma replace_var_for_let_simple_helper_helper :
  forall p1 p2 x1 x2 y A,
  forall IHx1 : (forall (y : Rml) (n : nat) (A B : Type),
               rml_valid_type A x1 [:: (n, B)] ->
               rml_is_simple (@replace_var_for_let_aux y [::]) ->
               rml_is_simple
                 (replace_var_with_value (@replace_var_for_let_aux x1 [:: (n,B)])
                                         (n, B) (@replace_var_for_let_aux y [::]))),
  forall IHx2 : (forall (y : Rml) (n : nat) (A B : Type),
               rml_valid_type A x2 [:: (n, B)] ->
               rml_is_simple (@replace_var_for_let_aux y nil) ->
               rml_is_simple
                 (replace_var_with_value (@replace_var_for_let_aux x2 [:: (n,B)]) 
                                         (n, B) (@replace_var_for_let_aux y nil))),
    rml_valid_type A (Let_stm p1 x1 x2) [:: p2]
    ->
    rml_is_simple (@replace_var_for_let_aux y nil)
    ->
    rml_is_simple
    (replace_var_with_value
       (replace_var_with_value
          (@replace_var_for_let_aux x2 (p1 :: p2 :: nil))
          p1
          (@replace_var_for_let_aux x1 [:: p2]))
       p2
       (@replace_var_for_let_aux y nil)).
Proof.
  intros.
  induction (replace_var_for_let_aux y).
  all: induction (replace_var_with_value (replace_var_for_let_aux x2) p1
                                         (replace_var_for_let_aux x1)).
  all: simpl.
  all: try easy ; try constructor.
  - destruct pselect ; simpl.
    + constructor.
    + Focus 2.
      destruct pselect.  
Admitted.

Lemma valid_env_weakening :
  forall l1 l2 p T, rml_valid_type T (Var p) l1 -> rml_valid_type T (Var p) (l1 ++ l2).
Proof.
  intros.
  inversion H ; subst.
  constructor.
  apply List.in_or_app.
  left.
  assumption.
Qed.
  
Lemma replace_var_for_let_simple_helper :
  forall (x y : Rml) n {A B},
    rml_valid_type A x ((n,B) :: nil) ->
    rml_is_simple (@replace_var_for_let_aux y nil) ->
    rml_is_simple (@replace_var_with_value (@replace_var_for_let_aux x ((n,B) :: nil)) (n,B) (@replace_var_for_let_aux y nil)).
Proof.
  induction x ; intros ; simpl.
  - destruct pselect ; simpl.
    + assumption.
    + destruct p.
      inversion H ; subst.
      simpl in *.
      inversion H5 ; contradiction.        
  - apply is_const.
  - apply replace_var_for_let_simple_helper_helper with (A := A) ; try assumption.
  - inversion H ; subst.
    apply is_if.
    + apply IHx1 with (A := bool) ; assumption.
    + apply IHx2 with (A := A) ; assumption.
    + apply IHx3 with (A := A) ; assumption.
  - inversion H ; subst.
    apply is_app.
    + apply IHx1 with (A := (T -> A)) ; assumption.
    + apply IHx2 with (A := T) ; assumption.
Defined.

Theorem replace_var_for_let_simple :
  forall (x : Rml) {A} `{x_valid : rml_valid_type A x nil},
  rml_is_simple (@replace_var_for_let x (@valid_is_well x A nil x_valid)).
Proof.  
  unfold replace_var_for_let.
  induction x ; intros.
  - apply valid_var_nil_is_false in x_valid ; contradiction.
  - simpl.
    apply is_const.
  - simpl.
    inversion x_valid ; subst.
    apply replace_var_for_let_simple_helper with (A := A).
    + assumption.
    + apply (IHx1 B).
      assumption.
  - simpl.
    inversion x_valid ; subst.
    apply is_if ; auto 2 using (IHx1 bool), (IHx2 A), (IHx3 A).
  - simpl.
    inversion x_valid ; subst.
    apply is_app ; auto 2 using (IHx1 (T -> A)), (IHx2 T).
Defined.

Lemma replace_var_for_let_valid_helper_helper :
  forall p (x1 x2 y : Rml) n {A B} l,
    rml_valid_type A
        (replace_var_with_value (@replace_var_for_let_aux x2 (p :: (n,B) :: l)) p
           (@replace_var_for_let_aux x1 ((n,B) :: l))) ((n, B) :: l) ->
    rml_valid_type B (@replace_var_for_let_aux y l) l ->
  rml_valid_type A
    (replace_var_with_value
       (replace_var_with_value (@replace_var_for_let_aux x2 (p :: (n,B) :: l)) p (@replace_var_for_let_aux x1 ((n,B) :: l)))
       (n, B) (@replace_var_for_let_aux y l)) l.
Proof.
Admitted.

Lemma replace_var_for_let_valid_helper :
  forall (x y : Rml) n {A B} l,
    rml_valid_type A (@replace_var_for_let_aux x ((n,B) :: l)) ((n,B) :: l) ->
    rml_valid_type B (@replace_var_for_let_aux y l) l ->
    rml_valid_type A (@replace_var_with_value (@replace_var_for_let_aux x ((n,B) :: l)) (n,B) (@replace_var_for_let_aux y l)) l.
Proof.
  induction x ; simpl ; intros.
  - inversion H ; subst.
    simpl.
    destruct pselect ; simpl.
    + inversion e ; subst.
      assumption.
    + inversion H3.
      * easy.
      * apply valid_var.
        assumption.
  - apply valid_const.
    inversion H ; subst.
    easy.
  - simpl.
    apply replace_var_for_let_valid_helper_helper ; assumption. (* TODO *)
  - inversion H ; subst.
    apply valid_if.
    + apply IHx1 ; assumption.
    + apply IHx2 ; assumption.
    + apply IHx3 ; assumption.
  - inversion H ; subst.
    apply valid_app.
    + apply IHx1 ; assumption.
    + apply IHx2 ; assumption.
Defined.

Theorem replace_var_for_let_valid :
  forall (x : Rml) {A} l `{x_valid : rml_valid_type A x l},
    rml_valid_type A (@replace_var_for_let_aux x l) l.
Proof.
  induction x ; intros.
  - inversion x_valid ; subst.
    easy.
  - simpl.
    apply valid_const.
    inversion x_valid ; subst.
    reflexivity.
  - simpl.
    inversion x_valid ; subst.
    pose (@replace_var_for_let_valid_helper x2 x1 x A B l).
    apply r.
    + apply IHx2.
      assumption.
    + apply IHx1.
      assumption.
  - simpl.
    inversion x_valid ; subst.
    apply valid_if.
    + apply IHx1 ; assumption.
    + apply IHx2 ; assumption.
    + apply IHx3 ; assumption.
  - simpl.
    inversion x_valid ; subst.
    apply valid_app.
    + apply IHx1 ; assumption.
      apply IHx2 ; assumption.
Defined.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A x nil} : continuation_monad_type R A :=
  let y := @replace_var_for_let x (@valid_is_well x A nil x_valid) in
  let y_simple := @replace_var_for_let_simple x A x_valid in
  let y_valid := @replace_var_for_let_valid x A nil x_valid in
  (interp_srml (@rml_to_sRml A y y_simple y_valid)).