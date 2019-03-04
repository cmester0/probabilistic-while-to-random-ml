From mathcomp Require Import all_ssreflect all_algebra.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

Require Import Rml.

Check @cmd.

Check (vars_ _) _.

Inductive well_defined_pWhile : cmd -> Prop :=
| well_def_skip : well_defined_pWhile skip
| well_def_abort : well_defined_pWhile skip
| well_def_assign : forall {t} (x : (vars_ _) t) e, well_defined_pWhile (assign x e).

Definition initial_env : forall T, vars T -> nat :=
  fun T y => 0. (* Return is always 0 *)

Fixpoint extend_env {T} (x : vars T) (v : nat) (env : forall T, vars T -> nat) : forall T, vars T -> nat :=
  fun U y =>
    if  vname x = vname y (* TODO: Make more precise *)
    then v
    else @env U y.

Example lookup_in_env :
  forall T x n, (extend_env x n initial_env) T x = n.
Proof.
  intros.
  destruct x.
  - simpl.
    destruct (s == s) eqn : s_old.
    * reflexivity.
    * easy.

Fixpoint translate_pWhile_expr_to_rml {T} (x : expr T) (env : forall T, vars T -> nat) :=
  match x with
  | var_ A n => Var (env A n)
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
    forall T x n, translate_pWhile_expr_to_rml (var_ x) (@extend_env T x n initial_env) = Var n.
Proof.
  intros.
  simpl.
  unfold extend_env.

  induction x eqn : old_x.
  - unfold initial_env.
    
    
    Locate "==".
    
    destruct (s == s) eqn : old_s.
    + reflexivity.
    + 
  
  destruct n.
  - induction x.
    + simpl.
      destruct (s == s).
      * reflexivity.
      * unfold initial_env.
        reflexivity.
    + simpl.
      
      
      
  
  reflexivity.
Qed.

Fixpoint translate_pWhile_cmd_to_rml (x : cmd) {T} (ret : vars T) (env : forall {T}, vars T -> nat) : Rml :=
  match x with
  | abort => Var (env ret)
  | skip => Var (env ret)
  | assign A n e => Let_stm (env n) (translate_pWhile_expr_to_rml e (@env)) (Var (env ret))
  | random A n e => Var (env ret)
  | cond b m1 m2 => Var (env ret)
  | while b e => Var (env ret)
  | seqc e1 e2 => Var (env ret)
  end.

Example translate_exp_cst :
    forall n, translate_pWhile_expr_to_rml (cst_ n) (@initial_env) = Const nat n.
Proof.
  intros.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.


Example translate_assignment :
  forall x,
    translate_pWhile_cmd_to_rml (assign x (cst_ 2)) x (@initial_env) = Const nat 2.
Proof.
  intros.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.
