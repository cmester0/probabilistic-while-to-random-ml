From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Require Import Rml.

(* -------------------------------------------------------------------- *)

Definition Choice T := (ChoiceType (EqType T gen_eqMixin) gen_choiceMixin).

Lemma choice_of_type_to_choice_type :
  forall {R : realType} (x : distr R (Choice bool)), distr R (bool_choiceType).
Proof.
Admitted.

Fixpoint ssem_aux {R : realType} {T : Type} (x : @sRml T) : distr R (Choice T) :=
  match x with
  | sConst c => @dunit R (Choice T) c
  | sIf_stm b m1 m2 =>
    let b'' := choice_of_type_to_choice_type (ssem_aux b) in
    \dlet_(b' <- b'') (if b' then ssem_aux m1 else ssem_aux m2)
  | sApp_stm A e1 e2 =>
    @dlet R (Choice (A -> T)) (Choice T) (fun t => @dlet R (Choice A) (Choice T) (fun u => @dunit R (Choice T) (t u)) (@ssem_aux R A e2)) (ssem_aux e1)
  end.

Fixpoint ssem {R} {T} (x : Rml) `{x_valid : rml_valid_type T x nil} : distr R (Choice T) :=
  let y := @replace_all_variables_type (Choice T) x x_valid in
  @ssem_aux R T y.