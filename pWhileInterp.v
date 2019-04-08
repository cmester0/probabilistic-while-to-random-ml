From mathcomp Require Import all_ssreflect all_algebra.
From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

From mathcomp.analysis Require Import boolp reals distr.

Require Import Rml.

Inductive well_defined_pWhile : cmd -> Prop :=
| well_def_skip : well_defined_pWhile skip
| well_def_abort : well_defined_pWhile skip
| well_def_assign : forall {t} (x : (vars_ _) t) e, well_defined_pWhile (assign x e).

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

Fixpoint translate_pWhile_expr_to_rml {T} (x : expr T) (ret : nat * Type * ident) (env : seq (nat * Type * ident)) : Rml :=
  match x with
  | var_ A n =>
    let v := @lookup n.(vname) ret env in
    Var v
  | cst_ A a => Const A a
  | prp_ m => Const bool true (* What does this mean? *)
  | app_ A B f x => App_stm B (translate_pWhile_expr_to_rml f ret (@env)) (translate_pWhile_expr_to_rml x ret (@env))
  end.  

Compute translate_pWhile_expr_to_rml (cst_ 4) (0,_,_) nil.
Compute (fun x => translate_pWhile_expr_to_rml (var_ x) (0,_,_) [:: (1,_,_)]).

(* -------------------------------------------------------------------------------- *)
  
Fixpoint translate_pWhile_cmd_to_rml (x : cmd) {T : Type} ret (env : seq (nat * Type * ident)) : Rml :=
  match x with
  | seqc (assign A n e) e2 =>
    Let_stm
      (lookup n.(vname) ret env)
      (translate_pWhile_expr_to_rml e ret env)
      (@translate_pWhile_cmd_to_rml e2 T ret env)
    
  | abort => Var (@lookup ret.2 ret env)
  | skip => Var (lookup ret.2 ret env)
  | assign A n e =>
    Let_stm
      (lookup n.(vname) ret env)
      (translate_pWhile_expr_to_rml e ret (@env))
      (Var (lookup ret.2 ret env))
      
  | random A n e => Var (lookup ret.2 ret env)
  | cond b m1 m2 =>
    If_stm
      (translate_pWhile_expr_to_rml b ret env)
      (@translate_pWhile_cmd_to_rml m1 T ret (@env))
      (@translate_pWhile_cmd_to_rml m2 T ret (@env))
      
  | while b e =>
    Let_rec
      (0,T) (* Todo correct index *)
      (@translate_pWhile_cmd_to_rml e T ret env)
      (translate_pWhile_expr_to_rml b ret (@env))
      
  | seqc e1 e2 =>
    Let_stm (999,Type)
      (@translate_pWhile_cmd_to_rml e1 T ret env)
      (@translate_pWhile_cmd_to_rml e2 T ret env)
  end.

(* -------------------------------------------------------------------------------- *)

Fixpoint extract_vars (cmd : @cmd_ _ cmem) : seq (ihbType * ident) :=
  match cmd with
  | abort | skip => [::]
  | (v <<- _)%S => [:: (v.(vtype), v.(vname))]
  | (v <$- _)%S => [:: (v.(vtype), v.(vname))]
  | (If _ then m1 else m2)%S => extract_vars m1 ++ extract_vars m2
  | (While _ Do c)%S => extract_vars c
  | (c1 ;; c2)%S => extract_vars c1 ++ extract_vars c2
  end.

Fixpoint make_env (mem : cmem) (all_vars : seq (ihbType * ident)) (counter : nat) : seq (nat * Type * ident) :=
  match all_vars with
  | nil => nil
  | x :: xs => (counter, Inhabited.sort x.1, x.2) :: make_env mem xs counter.+1
  end.
  
(* -------------------------------------------------------------------------------- *)
