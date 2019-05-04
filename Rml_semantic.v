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

Fixpoint ubn {R : realType} {A B : Type} (F : (A -> B) -> A -> B) (a : A) (n : nat) : distr R (Choice B) :=
  match n return distr R (Choice B) with
  | 0 => dnull
  | S n' => @dlet R (Choice A) (Choice B) (fun a => @ubn R A B F a n') (@dunit R (Choice A) a)
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
    
Fixpoint ssem_aux {R : realType} {T : Type} (x : @sRml T) (env : seq (nat * Type * (@mem_type R))) (x_valid : srml_valid_type T (map fst env) x) {struct x} : {distr (Choice T) / R}.
  destruct x.
  - refine (lookup env (n,T) (var_p_in_list n T env x_valid) T).
  - refine (@dunit R (Choice T) t).
  - assert (srml_valid_type C [:: p & [seq i.1 | i <- env]] x) by (apply helper3 in x_valid ; intros ; assumption).
    pose (fun k => ssem_aux R C x ((p,k) :: env) H).
    pose (fun k => rewrite_type T p.2 C R (
    @dlet R (Choice C) (Choice (p.2 -> C)) (fun c =>
    @dunit R (Choice (p.2 -> C)) (fun x =>
    c)) (ssem_aux R C x ((p,k) :: env) H)) e).

    refine (d0 (fun A => @dnull R (Choice A))).
  (* TODO, convert to a distribution function *)    
  - assert (srml_valid_type bool [seq i.1 | i <- env] x1) by (inversion x_valid ; assumption).
    assert (srml_valid_type T [seq i.1 | i <- env] x2) by (inversion x_valid ; assumption).
    assert (srml_valid_type T [seq i.1 | i <- env] x3) by (inversion x_valid ; assumption).
    refine (let b'' := choice_of_type_to_choice_type (ssem_aux _ _ x1 env H) in
            \dlet_(b' <- b'') (if b' then ssem_aux _ _ x2 env H0 else ssem_aux _ _ x3 env H1)).
  - apply helper in x_valid.
    inversion x_valid.    

    refine (@dlet R (Choice (T0 -> T)) (Choice T) (fun t =>
    @dlet R (Choice T0) (Choice T) (fun u =>
    @dunit R (Choice T) (t u)) (@ssem_aux R T0 x2 env H0)) (@ssem_aux R (T0 -> T) x1 env H)).
  - pose (x1' := sFun T (nx,B) (type_equality_reflexive (B -> T)) (sApp _ x1 (sVar nx))).
    pose (x1'' := sFun (B -> T) (nf,B -> T) (type_equality_reflexive ((B -> T) -> B -> T)) x1').

    assert (srml_valid_type ((B -> T) -> B -> T) [seq i.1 | i <- env] x1'') by (apply helper2 in x_valid ; inversion x_valid ; repeat constructor ; try left ; easy).
    
    pose (sf := ssem_aux R _ x1'' env H).

    pose (x2' := sFun B (nf,B -> T) (type_equality_reflexive ((B -> T) -> B)) x2).
    assert (srml_valid_type ((B -> T) -> B) [seq i.1 | i <- env] x2').
    constructor.
    apply helper2 in x_valid.
    inversion x_valid.
    assumption.
    
    pose (sx := ssem_aux R _ x2' env H0).

    assert (srml_valid_type B ((nx,B) :: [seq i.1 | i <- env]) (sVar nx)).
    constructor. left. reflexivity.
    
    pose (ssem_aux R _ (sVar nx) ((nx,B,fun A => @dnull R (Choice A)) :: env) H1).
    pose (fun b => @dlet R (Choice ((B -> T) -> B -> T)) (Choice T) (fun x => dlim (ubn x b)) sf).

    pose (@dlet R (Choice B) (Choice T) (fun k => d0 k) d).
    refine d1.
Qed.

Fixpoint ssem {R : realType} {T : Type} (x : Rml) `{x_valid : rml_valid_type T nil _ x} : {distr (Choice T) / R} :=
  let y := @replace_all_variables_type T x x_valid in
  @ssem_aux R T y nil.