From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.

Require Import Rml.
Require Import Rml_semantic.

(** * Examples **)

Definition some : Rml :=
  Let_rec nat nat 0 1
          (Random (Var (1,nat <: Type) true))
          (Const 10).

Definition some_valid : rml_valid_type nat nil nil some.
Proof.
  assert (check_valid nat nil nil some = true).
  native_compute.
  destruct boolp.pselect.
  reflexivity.
  contradiction.

  apply type_checker.
  assumption.
Qed.

Definition some_valid2 : rml_valid_type nat nil nil some.
  constructor.
  - constructor.
    + apply (valid_fun_var nil [:: (1,nat <: Type); (0,nat -> nat <: Type)] (1,nat <: Type)).
      left.
      reflexivity.
    + constructor.
Defined.

Compute (@replace_all_variables_aux_type nat some nil nil (env_nil nil) some_valid).
Compute (@replace_all_variables_aux_type nat some nil nil (env_nil nil) some_valid2).

Check @ssem_aux _ nat (sFix nat 0 1 (sRandom _ (sVar 1)) (sConst 10)) nil (svalid_fix nat [::] nat 0 1 (sRandom _ (sVar 1)) 
            (sConst 10)
            (svalid_random nat [:: (1, nat <: Type); (0, nat -> nat  <: Type)] 
               (sVar 1) _
               (svalid_fun_var nat [:: (1, nat <: Type); (0, nat -> nat <: Type)] 1
                  _)) (svalid_const nat [::] 10)).

Compute @ssem_aux _ nat (sConst 10) nil (svalid_const nat nil 10).
Check @ssem.

From xhl Require Import pwhile.pwhile.

Compute @ssem R nat (Const 10) (valid_const nat nil nil 10).

Lemma is10 :
  @ssem R nat (Const 10) (valid_const nat nil nil 10) = @dunit R (Choice nat) 10.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma is_random :
  @ssem R nat (Random (Const 10)) (valid_random nil nil (Const 10) (valid_const nat nil nil 10)) = @duni R (Choice nat) (range 10).
Proof.
  simpl.
  compute.
  native_compute.
  reflexivity.
Qed.
