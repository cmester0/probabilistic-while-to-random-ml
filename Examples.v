From mathcomp Require Import all_ssreflect all_algebra.
Require Import Util.


Require Import Rml.

Definition fib_f := (@pair nat Type 0 (nat->nat)).
Definition fib_x := (@pair nat Type 1 nat).
Definition fib_sub1 :=
  (App_stm nat (Var fib_f) (App_stm nat (Const (nat -> nat) (fun x => x - 1)) (Var fib_x))).
Definition fib_sub2 :=
  (App_stm nat (Var fib_f) (App_stm nat (Const (nat -> nat) (fun x => x - 2)) (Var fib_x))).
Definition fib_rec :=
  (App_stm nat (App_stm (nat -> nat) (Const (nat -> nat -> nat) (fun x y => x + y))
                      fib_sub1) fib_sub2).
Definition fib :=
  Let_rec fib_f fib_x
          (If_stm (App_stm nat (Const (nat -> bool) (fun x => x == 0)) (Var fib_x))
                  (Const nat 1)
                  fib_rec)
          (App_stm nat (Var fib_f) (Const nat 10)).

Compute rml_to_sRml_l fib nil nil.


Require Import Rml_semantic.

(** * Examples **)

Compute (fix even (n : nat) := match n with | 0 => 0 | S n' => odd n' end
                                                      with odd (n : nat) := match n with | 0 => 1 | S n' => even n' end for even) 5.


Fixpoint a (t : nat) : nat
with b (t : nat) : nat.
Proof.
  exact 0.
  exact 1.
Defined.
