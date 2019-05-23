From mathcomp Require Import all_ssreflect all_algebra.
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

From xhl Require Import pwhile.pwhile.

Check @ssem R nat some some_valid.
Compute @ssem R nat some some_valid.

Check ssem (Const 3).
Check @replace_all_variables_type nat (Const 3) (valid_const nat nil nil 3).
Compute @replace_all_variables_type nat (Const 3) (valid_const nat nil nil 3).


Check (valid_rml_makes_valid_srml nat (Const nat 3) (sConst 3) nil nil (valid_const nat nil nil 3)).
Compute (valid_rml_makes_valid_srml nat (Const nat 3) (sConst 3) nil nil (valid_const nat nil nil 3)).
Compute ssem_aux (sConst 3).

Definition walk : Rml :=
  Let_rec nat nat 0 1
          (If_stm Flip
                  (Var (1,nat <: Type))
                  (App_stm nat (Var (0,nat -> nat <: Type)) (App_stm nat (Const (nat -> nat) (fun x => x+1)) (Var (1,nat <: Type)))))
          (Const nat 0).

Definition walk_valid : rml_valid_type nat nil nil walk.
Proof.
  constructor.
  constructor.
  constructor.
  reflexivity.
  constructor 2.
  left.
  reflexivity.
  constructor.
  constructor 2.
  right.
  left.
  reflexivity.
  constructor.
  constructor.
  constructor 2.
  left.
  reflexivity.
  constructor.
Qed.

Check @ssem.
Check @ssem _ nat walk walk_valid.
Compute @ssem pwhile.R nat walk walk_valid.




Definition apps := (App_stm nat (Const (nat -> bool) (fun n => true)) (Const nat 10)).
Definition apps_valid : rml_valid_type bool [::] [::] apps.
Proof.
  constructor.
  constructor.
  constructor.
Qed.

Definition even_e1 := (App_stm nat (Const (nat -> bool) (fun n => true)) (Var (1,nat <: Type))).
Definition even_e2 := (Const nat 4).

Definition even := Let_rec nat bool 0 1 even_e1 even_e2.

Definition even_valid : rml_valid_type bool [::] [::] even.
Proof.
  constructor.
  constructor.
  constructor.
  constructor 2.
  left.
  reflexivity.
  constructor.
Qed.
  
Check @replace_all_variables_type bool even even_valid.
Check (fun R => @ssem R bool even even_valid).
Compute (fun R => @ssem R bool even even_valid).

Definition prime_test := (* p = 0, n = 1 *)
  Let_rec nat bool 0 1
          (If_stm (App_stm nat (Const (nat -> bool) (fun n => n == 0)) (Var (1,nat <: Type)))
                  (Const bool true)
                  (Let_stm k = ))
.
