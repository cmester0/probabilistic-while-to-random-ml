From mathcomp Require Import all_ssreflect all_algebra.
Require Import Rml.

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