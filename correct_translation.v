From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Require Import Rml.
Require Import Rml_semantic.
Require Import pWhileInterp.

From xhl Require Import pwhile.pwhile.
From xhl Require Import pwhile.psemantic.
From xhl Require Import pwhile.inhabited.

Compute @translate_pWhile_expr_to_rml nat (cst_ 4) _ nil.
Compute @Rml_semantic.ssem pwhile.R _ (Rml.Const nat 4) (@valid_const nat nil 4).
Check Rml_semantic.ssem (@translate_pWhile_expr_to_rml nat (cst_ 4) _ nil) _.

Check rml_valid_type nat [::] (translate_pWhile_expr_to_rml (cst_ 4) _ nil).

Require Import Util.

Definition nat2 : Type := nat.

Compute compute_valid nat nil (Let_stm (1, nat2) (Const nat 4) (Rml.Var (1, nat2))) >>= (fun x_valid => Some (@replace_all_variables_type nat (Let_stm (1, _) (Const nat 4) (Rml.Var (1, _))) x_valid)).

Lemma some_help :
    compute_valid nat nil (Let_stm (1, nat2) (Const nat 4) (Rml.Var (1, nat2))) >>= (fun x_valid =>
    Some (@replace_all_variables_type nat (Let_stm (1, _) (Const nat 4) (Rml.Var (1, _))) x_valid))
    = Some (sConst 4).
Proof.
  intros.
  simpl.
  unfold ob.
  
  elim (@pselect_left_eq Type nat) ; intros x H
  rewrite H ; clear H.
    
  destruct (pselect_left_eq (@pair nat Type 1 nat)).
  rewrite H ; clear H.
Qed.
  
      

Lemma sudo_valid :
  forall T ih x y z x_valid,
    @interp_rml nat (@translate_pWhile_cmd_to_rml (x <<- (cst_ 4))%S T (0,T,@vname _ ih y)
                                                [:: (1,T,@vname _ ih z)]) nat x_valid id
    = 4.
Proof.
  intros.
  simpl.
  inversion x_valid ; subst.
  simpl in *.
  destruct pselect.
  - destruct pselect.
    + inversion H.
      subst.
      unfold replace_all_variables_type.
      simpl.
      destruct (pselect_left_eq (1,T)).
      rewrite H0 ; clear H0.
      simpl.
      compute.
      
      
      inversion H3 ; subst.
Qed.


Theorem commuting_translations_expr :
  forall T (e : @expr T) (mem : cmem)
    (ret : nat * Type * ident) (env : seq (nat * Type * ident))
    (x_valid : rml_valid_type T (translate_pWhile_expr_to_rml e ret env) [::]),
    @Rml_semantic.interp_rml T (translate_pWhile_expr_to_rml e ret env) T x_valid id =
    @esem _ _ T e mem .
Proof.
  induction e.
  
Admitted.

Theorem commuting_translations :
  forall (T : Type)
    (cmd : @cmd_ _ cmem) (mem : cmem) env `{env = (make_env mem (extract_vars cmd) 0)}
    (ret : nat * Type * ident) (_ : ret_env ret env)
    (x_valid : rml_valid_type T (translate_pWhile_cmd_to_rml cmd ret env) [::])
    val,
    @Rml_semantic.ssem pwhile.R _ (@translate_pWhile_cmd_to_rml cmd T ret env) x_valid val =
    ssem cmd mem mem.
Proof.
  induction cmd ; intros.
  - inversion x_valid ; subst.
    contradiction.
  - simpl.
    inversion x_valid ; subst.
    contradiction.
  - simpl in *.
    inversion H ; subst.
    simpl.
    destruct v.
    + simpl.
      destruct ret.
      simpl.
      inversion x_valid ; subst.
      * destruct pselect in H.
        -- inversion H.
           simpl.
           subst.
           simpl.
           destruct p.
           simpl.
           simpl in *.
           inversion H0 ; subst.
           unfold replace_all_variables_type.
    