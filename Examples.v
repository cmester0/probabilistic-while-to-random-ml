From mathcomp Require Import all_ssreflect all_algebra.
Require Import Util.

Require Import Rml.
Require Import Rml_semantic.


Definition apps := (App_stm nat (Const (nat -> bool) (fun n => true)) (Const nat 10)).
Definition apps_valid : rml_valid_type bool [::] [::] apps.
Proof.
  constructor.
  constructor.
  constructor.
Qed.

Compute (@ssem _ bool apps apps_valid).

Definition even_e1 := (App_stm nat (Const (nat -> bool) (fun n => true)) (Var (0,nat <: Type))).
Definition even_e2 := (Const nat 4).

Definition even := Let_rec nat bool 0 1 even_e1 even_e2.

Definition even_valid : rml_valid_type bool [::] [::] even.
Proof.
  constructor.
  constructor.
  constructor.
Qed.
  
Check @replace_all_variables_type bool even even_valid.

Require Import Rml_semantic.

Compute @ssem _ bool even even_valid.

(** * Examples **)

Compute (fix even (n : nat) := match n with | 0 => 0 | S n' => odd n' end
                                                      with odd (n : nat) := match n with | 0 => 1 | S n' => even n' end for even) 5.


Fixpoint a (t : nat) : nat
with b (t : nat) : nat.
Proof.
  exact 0.
  exact 1.
Defined.


Definition prime_test := (* p = 0, n = 1 *)
  Let_rec nat bool 0 1
          (If_stm (App_stm nat (Const (nat -> bool) (fun n => n == 0)) (Var (1,nat <: Type)))
                  (Const bool true)
                  (Let_stm k = ))
.
