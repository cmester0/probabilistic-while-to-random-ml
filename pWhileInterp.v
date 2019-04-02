From mathcomp Require Import all_ssreflect all_algebra.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

From mathcomp.analysis Require Import boolp reals distr.

Require Import Rml.

Inductive well_defined_pWhile : cmd -> Prop :=
| well_def_skip : well_defined_pWhile skip
| well_def_abort : well_defined_pWhile skip
| well_def_assign : forall {t} (x : (vars_ _) t) e, well_defined_pWhile (assign x e).

Check List.In.

Inductive ret_env : nat * Type * ident -> seq (nat * Type * ident) -> Prop :=
| ret_nil : forall x, ret_env x nil
| ret_cons : forall x a l, ret_env x l -> ret_env x (a :: l).

Definition to_ret_env ret env : ret_env ret env.
Proof.
  induction env.
  - constructor.
  - constructor.
    assumption.
Qed.

Fixpoint lookup (x : ident) (ret : nat * Type * ident) (env : seq (nat * Type * ident)) {struct env} : (nat * Type).
Proof.
  assert (ret_env : ret_env ret env) by apply (to_ret_env ret env).
  induction env.
  - refine (ret.1).
  - destruct (pselect (a.2 = x)).
    + refine a.1.
    + apply IHenv.
      inversion ret_env ; subst.
      assumption.
Defined.

Fixpoint translate_pWhile_expr_to_rml {T} (x : expr T) (ret : nat * Type * ident) (env : seq (nat * Type * ident)) :=
  match x with
  | var_ A n =>
    let v := @lookup n.(vname) ret env in
    Var v
  | cst_ A a => Const A a
  | prp_ m => Const bool true (* What does this mean? *)
  | app_ A B f x => App_stm B (translate_pWhile_expr_to_rml f ret (@env)) (translate_pWhile_expr_to_rml x ret (@env))
  end.  

Fixpoint translate_pWhile_cmd_to_rml (x : cmd) {T : Type} ret (env : seq (nat * Type * ident)) : Rml :=
  match x with
  | seqc (assign A n e) e2 =>
    Let_stm
      (lookup n.(vname) ret env)
      (translate_pWhile_expr_to_rml e ret (@env))
      (@translate_pWhile_cmd_to_rml e2 T ret env)
    
  | abort => Var (@lookup ret.2 ret env)
  | skip => Var (lookup ret.2 ret env)
  | assign A n e => Let_stm (lookup n.(vname) ret env) (translate_pWhile_expr_to_rml e ret (@env)) (Var (lookup ret.2 ret env))
  | random A n e => Var (lookup ret.2 ret env)
  | cond b m1 m2 =>
    If_stm
      (translate_pWhile_expr_to_rml b ret (@env))
      (@translate_pWhile_cmd_to_rml m1 T ret (@env))
      (@translate_pWhile_cmd_to_rml m2 T ret (@env))
      
  | while b e => Var (lookup ret.2 ret env)
  | seqc e1 e2 =>
    Let_stm (999,Set)
      (@translate_pWhile_cmd_to_rml e1 T ret env)
      (@translate_pWhile_cmd_to_rml e2 T ret env)
  end.
