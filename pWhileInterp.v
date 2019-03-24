From mathcomp Require Import all_ssreflect all_algebra.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

Require Import Rml.
Require Import Rml_semantic.

From mathcomp.analysis Require Import boolp reals distr.

Inductive well_defined_pWhile : cmd -> Prop :=
| well_def_skip : well_defined_pWhile skip
| well_def_abort : well_defined_pWhile skip
| well_def_assign : forall {t} (x : (vars_ _) t) e, well_defined_pWhile (assign x e).

Definition initial_env p : ident -> (nat * Type) :=
  fun y => p. (* Return is always (0,Set), make better default (return var name) *)

Fixpoint extend_env (x : ident) (v : (nat * Type)) (env : ident -> (nat * Type)) : ident -> (nat * Type) :=
  fun y =>
    if pselect (y = x)
    (* @mget _ k (x%V).(vtype) m (x%V).(vname) == @mget _ _ (y%V).(vtype) m (y%V).(vname) *)
    then v
    else env y.

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
Qed.

Fixpoint translate_pWhile_expr_to_rml {T} (x : expr T) (env : ident -> (nat * Type)) :=
  match x with
  | var_ A n =>
    Var (env n.(vname))
  | cst_ A a => Const A a
  | prp_ m => Const bool true (* What does this mean? *)
  | app_ A B f x => App_stm B (translate_pWhile_expr_to_rml f (@env)) (translate_pWhile_expr_to_rml x (@env))
  end.  

Fixpoint translate_pWhile_cmd_to_rml (x : cmd) {T} (ret : vars T) (env : ident -> (nat * Type)) : Rml :=
  match x with
  | seqc (assign A n e) e2 =>
    Let_stm (env n.(vname)) (translate_pWhile_expr_to_rml e (@env)) (translate_pWhile_cmd_to_rml e2 ret env)
    
  | abort => Var (env ret.(vname))
  | skip => Var (env ret.(vname))
  | assign A n e => Let_stm (env n.(vname)) (translate_pWhile_expr_to_rml e (@env)) (Var (env ret.(vname)))
  | random A n e => Var (env ret.(vname))
  | cond b m1 m2 => If_stm (translate_pWhile_expr_to_rml b (@env)) (translate_pWhile_cmd_to_rml m1 ret (@env)) (translate_pWhile_cmd_to_rml m2 ret (@env)) 
  | while b e => Var (env ret.(vname))
  | seqc e1 e2 => Let_stm (999,Set) (translate_pWhile_cmd_to_rml e1 ret env) (translate_pWhile_cmd_to_rml e2 ret env)
  end.
