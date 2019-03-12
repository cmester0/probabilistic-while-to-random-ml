From mathcomp Require Import all_ssreflect all_algebra.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

Require Import Rml.

From mathcomp.analysis Require Import boolp reals distr.

Check @cmd.

Check (vars_ _) _.

Inductive well_defined_pWhile : cmd -> Prop :=
| well_def_skip : well_defined_pWhile skip
| well_def_abort : well_defined_pWhile skip
| well_def_assign : forall {t} (x : (vars_ _) t) e, well_defined_pWhile (assign x e).

Definition initial_env : ident -> nat :=
  fun y => 0. (* Return is always 0 *)

Check ident.

Fixpoint extend_env (x : ident) (v : nat) (env : ident -> nat) : ident -> nat :=
  fun y =>
    if pselect (y = x)
    (* @mget _ k (x%V).(vtype) m (x%V).(vname) == @mget _ _ (y%V).(vtype) m (y%V).(vname) *)
    then v
    else env y.

Check ident.

Theorem get_set :
  forall m x v, (@extend_env x v m) x = v.
Proof.
  intros.
  induction v.
  - simpl.
    case (pselect _).
    + intros.
      reflexivity.
    + intros.
      easy.
  - simpl.
    case (pselect _).
    + intros.
      reflexivity.
    + intros.
      easy.
Qed.

Fixpoint translate_pWhile_expr_to_rml {T} (x : expr T) (env : ident -> nat) :=
  match x with
  | var_ A n =>
    Var (env n.(vname))
  | cst_ A a => Const A a
  | prp_ m => Const bool true (* What does this mean? *)
  | app_ A B f x => App_stm B (translate_pWhile_expr_to_rml f (@env)) (translate_pWhile_expr_to_rml x (@env))
  end.  

Example translate_exp_cst :
    forall n, translate_pWhile_expr_to_rml (cst_ n) (initial_env) = Const nat n.
Proof.
  intros.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.

Example translate_exp_var :
    forall T x n, translate_pWhile_expr_to_rml (var_ x) (@extend_env (@vname _ T x) n initial_env) = Var n.
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
  - simpl.
    case (pselect _).
    + intros.
      simpl.
      reflexivity.
    + intros.
      easy.
Qed.

Fixpoint translate_pWhile_cmd_to_rml (x : cmd) {T} (ret : vars T) (env : ident -> nat) : Rml :=
  match x with
  | seqc (assign A n e) e2 => Let_stm (env n.(vname)) (translate_pWhile_expr_to_rml e (@env)) (translate_pWhile_cmd_to_rml e2 ret env)
    
  | abort => Var (env ret.(vname))
  | skip => Var (env ret.(vname))
  | assign A n e => Let_stm (env n.(vname)) (translate_pWhile_expr_to_rml e (@env)) (Var (env ret.(vname)))
  | random A n e => Var (env ret.(vname))
  | cond b m1 m2 => If_stm (translate_pWhile_cmd_to_rml b) (translate_pWhile_cmd_to_rml b) (translate_pWhile_cmd_to_rml b) 
  | while b e => Var (env ret.(vname))
  | seqc e1 e2 => Let_stm 999 (translate_pWhile_cmd_to_rml e1 ret env) (translate_pWhile_cmd_to_rml e2 ret env)
  end.

Example translate_cmd_cst :
    forall x (n1 n2 : nat), translate_pWhile_cmd_to_rml (seqc (assign x (cst_ n1)) (assign x (cst_ n2))) x (@initial_env) = Let_stm 0 (Const nat n1) (Let_stm 0 (Const nat n2) (Var 0)).
Proof.
  intros.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.