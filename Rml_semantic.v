From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Require Import Rml.

From xhl Require Import pwhile.pwhile.
From xhl Require Import pwhile.psemantic.

Require Import Util.

(* -------------------------------------------------------------------------------- *)

Definition Choice T := (ChoiceType (EqType T gen_eqMixin) gen_choiceMixin).

Lemma choice_of_type_to_choice_type :
  forall {R : realType} (x : distr R (Choice bool)), distr R (bool_choiceType).
Proof.
Admitted.

(* -------------------------------------------------------------------------------- *)

Definition mem_type {R} := forall A, distr R (Choice A).
Definition new_element {R A} (x : distr R (Choice A)) : @mem_type R.
Proof.
  refine (fun (B : Type) => _).
  destruct (pselect (A = B)).
  - subst.
    exact x.
  - exact (@dnull R (Choice B)).
Defined.

Fixpoint lookup {R} (env : seq (nat * Type * @mem_type R))
         (p : nat * Type) `(_ : List.In p (map fst env)) {struct env} :
  @mem_type R.
Proof.
  induction env.
  - contradiction.
  - simpl in H.
    destruct (pselect (a.1 = p)).
    + exact a.2.
    + assert (List.In p [seq i.1 | i <- env]) by (inversion H ; easy).
      intros.
      apply IHenv.
      assumption.
Qed.

Fixpoint ubn {R : realType} {A B : Type} (F : distr R (Choice ((A -> B) -> A -> B))) (n : nat) : distr R (Choice (A -> B)) :=
  match n return distr R (Choice (A -> B)) with
  | 0 => dnull
  | S n' =>
    @dlet R (Choice (A -> B)) (Choice (A -> B)) (fun G =>
    @dlet R (Choice ((A -> B) -> A -> B)) (Choice (A -> B)) (fun H =>
    @dunit R (Choice (A -> B)) (H G)) F) (ubn F n')
  end.

Lemma rewrite_type :
  forall T A C R (x : distr R (Choice (A -> C))), T = (A -> C) -> distr R (Choice T).
Proof.
  intros.
  subst.
  assumption.
Qed.

Lemma type_equality_reflexive :
  forall A : Type, A = A.
Proof. reflexivity. Qed.

Lemma var_p_in_list :
  forall {R : realType} (p : nat) (T : Type) (env : seq (nat * Type * (@mem_type R))),
    srml_valid_type T (map fst env) (sVar p) ->
    List.In (p, T) (map fst env).
Proof.
  intros.
  induction env.
  - inversion H.
    contradiction.
  - inversion H.
    assumption.
Qed.    

Lemma call_by_value_function :
  forall {R} A B (a : distr R (Choice (A -> B))),
    A -> distr R (Choice B).
Proof.
  intros.
  pose (@dlet R (Choice (A -> B)) (Choice B) (fun f => @dunit R (Choice B) (f X))).
  apply d.
  apply a.
Qed.

Lemma call_by_value_function' :
  forall {R} A B (a : A -> distr R (Choice B)) (X : A),
    distr R (Choice (A -> B)).
Proof.
  intros.
  pose (@dlet R (Choice B) (Choice (A -> B)) (fun b => @dunit R (Choice (A -> B)) (fun y => b))).
  apply d.
  apply a.
  apply X.
Qed.
  
Fixpoint ssem_aux {R : realType} {T : Type} (x : @sRml T) (env : seq (nat * Type * (@mem_type R))) (x_valid : srml_valid_type T (map fst env) x) {struct x} : {distr (Choice T) / R}.
  destruct x.
  (* sVar *)
  { refine (lookup env (n,T) (var_p_in_list n T env x_valid) T). }

  (* sConst *)
  { refine (@dunit R (Choice T) t). }

  (* sFun *)
  {
    assert (srml_valid_type C [:: p & [seq i.1 | i <- env]] x) by (apply helper3 in x_valid ; intros ; assumption).

    pose (fun (a : p.2) => ssem_aux R C x ((p,(new_element (@dunit R (Choice p.2) a))) :: env) H).
    pose (fun a => @call_by_value_function' R p.2 C a).

    pose (@dlet R (Choice p.2) (Choice (p.2 -> C)) (fun p2 : p.2 =>
      @dlet R (Choice C) (Choice (p.2 -> C)) (fun c =>
      d0 (fun p => dunit c) p2
      ) (d p2))).

    assert (T = (p.2 -> C)) by assumption ; subst ; clear H0.
    apply d1.
    apply dnull.
    (* TODO, convert to a distribution function *)    
  }

  (* sIf *)
  { assert (srml_valid_type bool [seq i.1 | i <- env] x1) by (inversion x_valid ; assumption).
    assert (srml_valid_type T [seq i.1 | i <- env] x2) by (inversion x_valid ; assumption).
    assert (srml_valid_type T [seq i.1 | i <- env] x3) by (inversion x_valid ; assumption).
    refine (let b'' := choice_of_type_to_choice_type (ssem_aux _ _ x1 env H) in
            \dlet_(b' <- b'') (if b' then ssem_aux _ _ x2 env H0 else ssem_aux _ _ x3 env H1)).
  }

  (* sApp *)
  {
    apply helper in x_valid.
    inversion x_valid.    
    refine (@dlet R (Choice (T0 -> T)) (Choice T) (fun t =>
    @dlet R (Choice T0) (Choice T) (fun u =>
    @dunit R (Choice T) (t u)) (@ssem_aux R T0 x2 env H0)) (@ssem_aux R (T0 -> T) x1 env H)).
  }

  (* sFix *)
  {
    Set Printing All.
    
    apply helper2 in x_valid.
    inversion_clear x_valid.

    pose (x2' := sFun T (nf,B -> C) (type_equality_reflexive _) x2).

    (* Manually proof function recursive step : *)

    (* T = (p.2 -> C) *)
    assert (valid_x2' : srml_valid_type ((B -> C) -> T) [seq i.1 | i <- env] x2') by (constructor ; assumption).
    
    assert (valid_x2 : srml_valid_type T ((nf, B -> C) :: [seq i.1 | i <- env]) x2) by (apply helper3 in valid_x2' ; assumption).

    pose (fun k => rewrite_type ((B -> C) -> T) (B -> C) T R (
    @dlet R (Choice T) (Choice ((B -> C) -> T)) (fun c =>
    @dunit R (Choice ((B -> C) -> T)) (fun x =>
    c)) (ssem_aux R T x2 ((nf,B -> C,k) :: env) valid_x2)) (type_equality_reflexive _)).

    pose (x := d (fun A => @dnull R (Choice A))). (* (B -> C) -> T *)
    (* End manually inserted proof *)

    pose (x1' := sFun C (nx,B) (type_equality_reflexive _) (sApp _ x1 (sVar nx))).
    pose (x1'' := sFun (B -> C) (nf,B -> C) (type_equality_reflexive _) x1').

    (* Manually proof function recursive step : *)

    assert (srml_valid_type ((B -> C) -> B -> C) [seq i.1 | i <- env] x1'').
    constructor.
    constructor.
    constructor.
    assumption.
    constructor.
    left.
    reflexivity.

    assert (valid_x1 : srml_valid_type (B -> C) ((nx,B) :: (nf, B -> C) :: [seq i.1 | i <- env]) x1) by (apply helper3 in H1 ; assumption).

    
    pose (fun k j =>
    @dlet R (Choice (B -> C)) (Choice (B -> C)) (fun c =>
    @dunit R (Choice (B -> C)) (fun x => c x))
    (ssem_aux R (B -> C) x1 ((nx,B,j) :: (nf,B -> C,k) :: env) valid_x1)).

    assert (valid_x1' : srml_valid_type (B -> C) ((nf, B -> C) :: [seq i.1 | i <- env]) x1') by (apply helper3 in H1 ; assumption).

    pose (fun k =>
    @dlet R (Choice (B -> C)) (Choice ((B -> C) -> B -> C)) (fun c =>
    @dunit R (Choice ((B -> C) -> B -> C)) (fun x => c))
    (ssem_aux R (B -> C) x1' ((nf,B -> C,k) :: env) valid_x1')).
    
    pose (f := d1 (fun A => @dnull R (Choice A))). (* (B -> C) -> B -> C *)
    (* End manually inserted proof *)

    (* ************************* *)

    intros.
    subst.

    refine (@dlet R (Choice (B -> C)) (Choice T) (fun f' =>
          @dlet R (Choice ((B -> C) -> T)) (Choice T) (fun x' : (B -> C) -> T =>
          @dunit R (Choice T) (x' f')) x) (dlim (ubn f))).
  }
Admitted.

Fixpoint ssem {R : realType} {T : Type} (x : Rml) `{x_valid : rml_valid_type T nil _ x} : {distr (Choice T) / R} :=
  let y := @replace_all_variables_type T x x_valid in
  @ssem_aux R T y nil (valid_rml_makes_valid_srml T x y nil nil x_valid).
