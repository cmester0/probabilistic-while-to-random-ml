Require Import Rml.
Require Import Rml_semantic.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Util.

(** * Examples **)

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
