(* -------------------------------------------------------------------- *)
(* ------- *) Require Import ClassicalFacts Setoid Morphisms.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

(* -------------------------------------------------------------------- *)
Require Import Rml.

(* -------------------------------------------------------------------- *)
Definition Choice T := (ChoiceType (EqType T gen_eqMixin) gen_choiceMixin).

Lemma adsf :
  forall {R : realType} (x : distr R (Choice bool)), distr R (bool_choiceType).
Proof.
Admitted.

Check adsf (@dunit _ (Choice bool) true).

Fixpoint ssem_aux {R : realType} {T : Type} (x : @sRml T) : distr R (Choice T) :=
  match x with
  | sConst c => @dunit R (Choice T) c
  | sIf_stm b m1 m2 =>
    let b'' := (adsf (ssem_aux b)) in
    \dlet_(b' <- b'') (if b' then ssem_aux m1 else ssem_aux m2)
  | sApp_stm A e1 e2 =>
    @dlet R (Choice (A -> T)) (Choice T) (fun t => @dlet R (Choice A) (Choice T) (fun u => @dunit R (Choice T) (t u)) (@ssem_aux R A e2)) (ssem_aux e1)
  end.

Fixpoint ssem R T (x : Rml) `{rml_valid_type T x nil} `{x_valid : rml_valid_type T x nil} : distr R (Choice T) :=
  let y := @replace_var_for_let x (@valid_is_well x T nil x_valid) in
  let y_simple := @replace_var_for_let_simple x T x_valid in
  let y_valid := @replace_var_for_let_valid x T nil x_valid in
  @ssem_aux R T (@rml_to_sRml T y y_simple y_valid).
