From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.
From xhl Require Import pwhile.pwhile.
From xhl Require Import pwhile.psemantic.
From xhl Require Import inhabited notations.

Require Import Rml.
Require Import Rml_semantic.
Require Import pWhileInterp.

(** * Examples **)

Definition nat_at_type : Type := nat.

Definition example : Rml :=
  (If_stm (Const bool true)
          (Let_stm
             (16,nat_at_type) (Const bool true)
             (Let_stm
                (12,nat_at_type) (Const nat 4)
                (If_stm (Var (16,nat_at_type)) (Var (12,nat_at_type)) (Const nat 10))))
          (Const nat 900)).

Compute replace_var_with_value example (16,nat_at_type) (Const bool true).
Compute replace_var_with_value example (12,_) (Const nat 4).   
Compute replace_var_for_let example.
Compute interp_rml example.

(* -------------------------------------------------------------------------------- *)

Compute @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil).
(* _ => bug *)

Compute @interp_rml _ (Let_stm (12,_) (@Const nat 4) (Var (12,_))) nat (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat _)).

Example const_4_interp :
  forall R Q, @interp_rml R (Let_stm (12,_) (@Const nat 4) (Var (12,_))) nat (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat Q)) = @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil).
Proof.
  simpl.
Admitted.

(** **)


Definition example_a := (@Const nat 4).
Definition example_b := (Var (12,nat_at_type)).
Definition example_let := (Let_stm (12,nat_at_type) example_a example_b).

Definition valid_a := (@valid_const nat nat 4 (@erefl Type nat) nil).
Check valid_a.
Definition valid_b : rml_valid_type nat example_b [:: (12, nat_at_type)].
Proof.
  refine (@valid_var 12 [:: (12, nat_at_type)] nat _).
  simpl.
  left.
  reflexivity.
Defined.
  
Definition valid_let' := (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil valid_a valid_b).

Compute @interp_rml _ example_let nat valid_let'.

Definition example_function := (fix contains_zero l :=
                                  match l with
                                  | nil => false
                                  | x :: xs => if x == 0
                                             then true
                                             else contains_zero xs end).
Definition example_list := 2 :: 3 :: 0 :: 4 :: 8 :: nil.

Definition example_e1 := (Const (list nat -> bool) example_function).
Definition example_e2 := (Const (list nat) example_list).

Definition example_valid1 := (@valid_const (list nat -> bool) (list nat -> bool) (example_function) (@erefl Type (list nat -> bool)) nil).
Definition example_valid2 := (@valid_const (list nat) (list nat) (example_list) (@erefl Type (list nat)) nil).

Compute @interp_rml _ (App_stm (list nat) example_e1 example_e2) bool (@valid_app bool (list nat) example_e1 example_e2 nil example_valid1 example_valid2).

Example translate_exp_cst :
    forall n p, translate_pWhile_expr_to_rml (cst_ n) (initial_env p) = Const nat n.
Proof.
  intros.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.

Example translate_exp_var :
    forall T x n p, translate_pWhile_expr_to_rml (var_ x) (@extend_env (@vname _ T x) n (initial_env p)) = Var n.
Proof.
  intros.
  simpl.
  destruct n.
  - simpl.
    case (pselect _).
    + intros.
      simpl.
      reflexivity.
    + intros.
      easy.
Qed.


Example translate_cmd_example1 :
  forall (T : Type) x (n1 n2 : nat),
    T = nat ->
    translate_pWhile_cmd_to_rml
      (seqc (assign x (cst_ n1)) (assign x (cst_ n2))) x (@initial_env (0,T))
    = Let_stm (0,T) (Const nat n1) (Let_stm (0,T) (Const nat n2) (Var (0,T))).
Proof.
  intros.
  subst.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.

Compute (fun x => translate_pWhile_cmd_to_rml (seqc (assign x (cst_ 4)) (assign x (cst_ 6))) x (@initial_env (0,_))).

(* translate_pWhile_cmd_to_rml (seqc (skip) (assign x (cst_ n))) x (@initial_env (0,T))) *)
