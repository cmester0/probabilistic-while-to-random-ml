From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.

From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

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
  - destruct (asbool (a.2 = x)).
    + refine a.1.
    + apply IHenv.
      inversion ret_env ; subst.
      assumption.
Defined.

Fixpoint translate_pWhile_expr_to_rml {T} (x : expr T) (ret : nat * Type * ident) (env : seq (nat * Type * ident)) : Rml :=
  match x with
  | var_ A n =>
    let v := @lookup n.(vname) ret env in
    Var v false
  | cst_ A a => Const a
  | prp_ m => Const true (* What does this mean? *)
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
    
  | abort => Var (@lookup ret.2 ret env) true
  | skip => Var (lookup ret.2 ret env) true
  | assign A n e =>
    Let_stm
      (lookup n.(vname) ret env)
      (translate_pWhile_expr_to_rml e ret (@env))
      (Var (lookup ret.2 ret env) true) 
      
  | random A n e => Random (Const (lookup n.(vname) ret env).1)
  | cond b m1 m2 =>
    If_stm
      (translate_pWhile_expr_to_rml b ret env)
      (@translate_pWhile_cmd_to_rml m1 T ret (@env))
      (@translate_pWhile_cmd_to_rml m2 T ret (@env))
      
  | while b e =>
    Let_rec
      T T 0 0 (* Todo correct index *)
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

Check expr.
Check translate_pWhile_expr_to_rml _ _ _.

Lemma translate_pWhile_expr_to_rml_valid :
  forall T (x : expr T) ret env,
    rml_valid_type T nil nil (translate_pWhile_expr_to_rml x ret env).
Admitted.

Check (If _ then _ else _)%S.
Locate "If _ then _ else _".

Inductive pwhile_valid {t mem} : cmd_ t mem -> Prop :=
| abort_valid : pwhile_valid (@abort t mem)
| skip_valid : pwhile_valid (@skip t mem)
| assign_valid : forall t0 v e, pwhile_valid (@assign t mem t0 v e)
| random_valid : forall t0 v e, pwhile_valid (@random t mem t0 v e)
| if_valid : forall b m1 m2, pwhile_valid (cond b m1 m2)
| while_valid : forall b e, pwhile_valid (while b e)
| seq_valid : forall e1 e2, pwhile_valid (e1 ;; e2)%S.

Lemma translate_pWhile_cmd_to_rml_valid :
  forall T (x : cmd) reti env (x_valid : pwhile_valid x),
    rml_valid_type T nil (map fst (env ++ [:: (0,T,reti)])) (@translate_pWhile_cmd_to_rml x T (0,T,reti) (env ++ [:: (0,T,reti)])).
Proof.
  intros.
  induction x.
  - simpl.
    induction env.
    + simpl.
      rewrite asboolT.
      apply (valid_fun_var nil [:: (0,T)] (0,T)).
      left.
      reflexivity.
      reflexivity.
    + 
    
    