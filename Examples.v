From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals distr.
Require Import Util.

Require Import Rml.
Require Import Rml_semantic.

(** * Helper **)

Fixpoint check_valid (A : Type) (vl : seq (nat * Type)) (fl : seq (nat * Type)) (x : Rml) {struct x} : bool :=
  match x with
  | Var p true => List.existsb (fun (a : nat * Type) => (p.1 == a.1) && asbool (p.2 = a.2)) fl && asbool (p.2 = A)
  | Var p false => List.existsb (fun (a : nat * Type) => (p.1 == a.1) && asbool (p.2 = a.2)) vl && asbool (p.2 = A)
  | Const A0 a => asbool (A = A0)
  | Let_stm p x1 x2 => check_valid p.2 vl fl x1 && check_valid A (p :: vl) fl x2
  | If_stm b m1 m2 => check_valid bool vl fl b && check_valid A vl fl m1 && check_valid A vl fl m2
  | App_stm T e1 e2 => check_valid (T -> A) vl fl e1 && check_valid T vl fl e2
  | Let_rec T T0 nf nx e1 e2 => check_valid A vl [:: (nx, T), (nf, T -> T0) & fl] e1 && check_valid T vl fl e2 && asbool (T0 = A)
  | Random x => check_valid nat vl fl x && asbool ((nat <: Type) = A)
  | Flip => asbool ((bool <: Type) = A)
  end.

Theorem type_checker :
  forall A vl fl x, check_valid A vl fl x = true <-> rml_valid_type A vl fl x.
Proof.
  assert (asbool_true : forall (k : Type), `[< k = k >] = true) by (intros ; apply (@asbool_equiv_eqP (k = k) true true) ; constructor ; easy ; easy).
  
  intros.
  split.
  { intros.
    generalize dependent fl.
    generalize dependent vl.
    generalize dependent A.
    induction x ; intros.
    { destruct b.
      {
        inversion H.
        rewrite H1.
        
        apply andb_prop in H1.
        inversion_clear H1.
        
        apply List.existsb_exists in H0.
        destruct H0.

        inversion_clear H0.
        
        apply andb_prop in H3.
        inversion_clear H3.

        apply asboolW in H2.
        apply asboolW in H4.

        apply PeanoNat.Nat.eqb_eq in H0.        
        subst.
        rewrite (surjective_pairing p).
        rewrite H0.
        rewrite H4.
        rewrite <- (surjective_pairing x).
        apply (valid_fun_var vl fl x).
        assumption.
      }
      {
        inversion H.

        apply andb_prop in H1.
        inversion_clear H1.

        apply List.existsb_exists in H0.
        destruct H0.
        
        inversion_clear H0.

        apply andb_prop in H3.
        inversion_clear H3.

        apply asboolW in H2.
        apply asboolW in H4.

        apply PeanoNat.Nat.eqb_eq in H0.

        rewrite (surjective_pairing p).
        rewrite H0.
        rewrite H4.
        rewrite <- (surjective_pairing x).

        subst.
        rewrite H4.

        apply (valid_var vl fl x).
        assumption.
      }  
    }
    {
      inversion H.
      apply asboolW in H1.
      subst.
      constructor.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply IHx1 in H0.
      apply IHx2 in H2.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply andb_prop in H0.
      inversion_clear H0.
      apply IHx1 in H1.
      apply IHx2 in H3.
      apply IHx3 in H2.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply IHx1 in H0.
      apply IHx2 in H2.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply andb_prop in H0.
      inversion_clear H0.
      apply asboolW in H2.
      apply IHx1 in H1.
      apply IHx2 in H3.
      subst.
      constructor ; assumption.
    }
    {
      inversion H.
      apply andb_prop in H1.
      inversion_clear H1.
      apply asboolW in H2.
      apply IHx in H0.
      subst.
      constructor ; assumption.
    }
    {
      inversion H.
      apply asboolW in H1.
      subst.
      constructor.
    }
  }
  {
    intros.
    generalize dependent fl.
    generalize dependent vl.
    generalize dependent A.
    induction x ; intros.
    {
      inversion H ; subst.
      {
        simpl.
        apply andb_true_intro.
        split.
        
        apply List.existsb_exists.
        exists p.
        split.

        assumption.

        apply andb_true_intro.
        split.
          
        apply eq_refl.
        apply (asbool_true p.2).

        apply (asbool_true p.2).
      }
      {
        simpl.
        apply andb_true_intro.
        split.
        
        apply List.existsb_exists.
        exists p.
        split.

        assumption.
        apply andb_true_intro.
          
        split.
        apply eq_refl.
        apply (asbool_true p.2).
        
        apply (asbool_true p.2).
      }
    }
    {
      inversion H ; subst.
      simpl.
      apply (asbool_true A).
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply IHx1.
      assumption.
      apply IHx2.
      assumption.
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply andb_true_intro.
      split.

      apply IHx1.
      assumption.
      apply IHx2.
      assumption.
      apply IHx3.
      assumption.
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply IHx1.
      assumption.
      apply IHx2.
      assumption.
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.

      apply andb_true_intro.
      split.

      apply IHx1 ; assumption.
      apply IHx2 ; assumption.
      apply (asbool_true T0).
    }
    {
      inversion H ; subst.
      simpl.
      apply andb_true_intro.
      split.
      
      apply IHx ; assumption.
      apply (asbool_true nat).
    }
    {
      inversion H ; subst.
      simpl.
      apply (asbool_true bool).
    }
  }
Defined.

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

Compute (@replace_all_variables_aux_type nat some nil nil (env_nil nil) some_valid).
Compute (@replace_all_variables_aux_type nat some nil nil (env_nil nil) some_valid2).

Check @ssem_aux _ nat (sFix nat 0 1 (sRandom _ (sVar 1)) (sConst 10)) nil (svalid_fix nat [::] nat 0 1 (sRandom _ (sVar 1)) 
            (sConst 10)
            (svalid_random nat [:: (1, nat <: Type); (0, nat -> nat  <: Type)] 
               (sVar 1) _
               (svalid_fun_var nat [:: (1, nat <: Type); (0, nat -> nat <: Type)] 1
                  _)) (svalid_const nat [::] 10)).

Compute @ssem_aux _ nat (sConst 10) nil (svalid_const nat nil 10).
Check @ssem.

From xhl Require Import pwhile.pwhile.

Compute @ssem R nat (Const 10) (valid_const nat nil nil 10).

Lemma is10 :
  @ssem R nat (Const 10) (valid_const nat nil nil 10) = @dunit R (Choice nat) 10.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma is_random :
  @ssem R nat (Random (Const 10)) (valid_random nil nil (Const 10) (valid_const nat nil nil 10)) = @duni R (Choice nat) (range 10).
Proof.
  simpl.
  compute.
  native_compute.
  reflexivity.
Qed.
