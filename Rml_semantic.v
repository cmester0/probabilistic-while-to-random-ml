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

(* Fixpoint ubn {R : realType} {A B : Type} (F : distr R (Choice ((A -> B) -> A -> B))) (n : nat) : distr R (Choice (A -> B)) := *)
(*   match n return distr R (Choice (A -> B)) with *)
(*   | 0 => dnull *)
(*   | S n' => *)
(*     @dlet R (Choice (A -> B)) (Choice (A -> B)) (fun G => *)
(*     @dlet R (Choice ((A -> B) -> A -> B)) (Choice (A -> B)) (fun H => *)
(*     @dunit R (Choice (A -> B)) (H G)) F) (ubn F n') *)
(*   end. *)

Fixpoint ubn {R : realType} {A B : Type} (F : (A -> distr R (Choice B)) -> A -> distr R (Choice B)) (n : nat) : A -> distr R (Choice B) :=
  fun a =>
  match n return distr R (Choice B) with
  | 0 => dnull
  | S n' => F (ubn F n') a
  end.

Definition ubn' {R} {A B} F a n := @ubn R A B F n a.

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

  (* sIf *)
  {
    assert (srml_valid_type bool [seq i.1 | i <- env] x1) by (inversion x_valid ; assumption).
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
    apply helper2 in x_valid.
    inversion_clear x_valid.

    (* x1 : B -> C *)
    (* f : ((B -> C) -> B -> C) *)
    
    pose (fx := sApp _ x1 (sVar nx)).

    assert (valid_fx : srml_valid_type C [:: (nx, B), (nf, B -> C) & [seq i.1 | i <- env]] fx).
    constructor.
    assumption.
    constructor.
    left.
    reflexivity.    

    pose (fun (k1 : B -> distr R (Choice C)) => call_by_value_function' B C k1).
    
    pose (f := fun (k1 : B -> distr R (Choice C)) => fun k2 => ssem_aux R C fx [:: (nx, B, (fun A => @dnull R (Choice A))), (nf, B -> C, new_element (call_by_value_function' B C k1 k2)) & env] valid_fx).

    pose (fun x => dlim (ubn' f x)).

    pose (call_by_value_function' B C d0).
    
    pose (fun xv => ssem_aux R T x2 [:: (nf, B -> C, new_element (d1 xv)) & env] H0).
    apply d2.
    
  }
Admitted.

Fixpoint ssem {R : realType} {T : Type} (x : Rml) `{x_valid : rml_valid_type T nil _ x} : {distr (Choice T) / R} :=
  let y := @replace_all_variables_type T x x_valid in
  @ssem_aux R T y nil (valid_rml_makes_valid_srml T x y nil nil x_valid).
