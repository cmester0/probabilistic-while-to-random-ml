From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Require Import Rml.

From xhl Require Import pwhile.pwhile.

Require Import Util.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_srml {A} {R} (x : @sRml A) : continuation_monad_type R A :=
  match x with
  | sConst c => unit c
  | sIf_stm b m1 m2 => (interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))
  | sApp_stm C e1 e2 => (interp_srml e1) >>= (fun (g : C -> A) => (interp_srml e2) >>= (fun k => unit (g k)))
  end.

(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A nil x} : continuation_monad_type R A := interp_srml (@replace_all_variables_type A x x_valid).

(* -------------------------------------------------------------------- *)

Definition Choice T := (ChoiceType (EqType T gen_eqMixin) gen_choiceMixin).

Lemma choice_of_type_to_choice_type :
  forall {R : realType} (x : distr R (Choice bool)), distr R (bool_choiceType).
Proof.
Admitted.

Fixpoint ssem_aux {R : realType} {T : Type} (x : @sRml T) : {distr (Choice T) / R} :=
  match x with
  | sConst c => @dunit R (Choice T) c
  | sIf_stm b m1 m2 =>
    let b'' := choice_of_type_to_choice_type (ssem_aux b) in
    \dlet_(b' <- b'') (if b' then ssem_aux m1 else ssem_aux m2)
  | sApp_stm A e1 e2 =>
    @dlet R (Choice (A -> T)) (Choice T) (fun t => @dlet R (Choice A) (Choice T) (fun u => @dunit R (Choice T) (t u)) (@ssem_aux R A e2)) (ssem_aux e1)
  end.

Fixpoint ssem {R : realType} {T : Type} (x : Rml) `{x_valid : rml_valid_type T nil x} : {distr (Choice T) / R} :=
  let y := @replace_all_variables_type T x x_valid in
  @ssem_aux R T y.