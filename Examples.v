Require Import Rml.
Require Import Rml_semantic.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import Util.

(** * Examples **)

Definition nat_at_type : Type := nat.
Definition bool_at_type : Type := bool.

Definition rml_ex1 :=
  (Let_stm
     (1,nat_at_type)
     (App_stm nat (Var (1,nat_at_type)) (Const nat 4))
     (Var (1,nat_at_type))).

Compute (compute_valid nat nil rml_ex1 >>= (fun x_valid =>
         Some (@interp_rml nat rml_ex1 nat x_valid))).

Example is_none :
  (compute_valid nat nil rml_ex1 >>= (fun x_valid => Some (@interp_rml nat rml_ex1 nat x_valid)))
  = None.
Proof.
  simpl.
  unfold eq_rec_r.
  unfold eq_rec.
  unfold eq_rect.
  unfold Logic.eq_sym.
  reflexivity.
Qed.
  
Example is_some :
  @interp_rml' nat (Let_stm
                    (1,nat_at_type)
                    (App_stm nat (Const (nat -> nat) id) (Const nat 4))
                    (Var (1,nat_at_type))) _ = Some (@^~ 4).
Proof.
  simpl.
  unfold ob.
  simpl.
  destruct boolp.pselect.
  destruct boolp.pselect.
  simpl.
  destruct (boolp.pselect ((1, nat_at_type) = (1, nat_at_type))).
  

Compute @interp_rml' _ (Let_stm
                         (1,nat_at_type)
                         (Const (nat -> nat) (fun x => 4))
                         (Let_stm
                            (1,nat_at_type)
                            (If_stm (App_stm nat (Const (nat -> bool) (fun x => x > 10)) (Var (1,nat_at_type))) (Const (nat -> nat) id) (Var (1,nat_at_type)))
                         (App_stm nat (Var (1,nat_at_type)) (Const nat 3)))) _.

Compute @interp_rml _ (Let_rec
                         (1,nat_at_type)
                         (If_stm (App_stm nat (Const (nat -> bool) (fun x => x > 10)) (Var (1,nat_at_type))) (Const (nat -> nat) id) (Var (1,nat_at_type)))
                         (App_stm nat (Var (1,nat_at_type)) (Const nat 3))).

Compute @interp_rml _ (Const nat 4) nat (@valid_const nat nil nat 4 (@erefl Type nat)).

Definition az :
  List.In (4,nat_at_type) [:: (4,nat_at_type)].
Proof.
  left.
  reflexivity.
Qed.

Check @replace_all_variables_type.
Compute (@replace_all_variables_type
           nat_at_type
           (@Let_stm (4, nat_at_type) (@Const nat_at_type 4)
                    (@Var (4, nat_at_type)))
           (@valid_let
              nat_at_type nil nat_at_type 4
              (@Const nat_at_type 4)
              (@Var (4,nat_at_type))
              (@valid_const nat_at_type nil nat_at_type 4 (@erefl Type nat_at_type))
              (@valid_var nat_at_type [:: (4,nat_at_type)] 4 az))
        ).


Compute @interp_rml _
        (Let_stm (4,nat_at_type) (Const nat 4) (Var (4,nat_at_type)))
        nat
        (valid_let nat nil nat 4
                   (Const nat 4)
                   (Var (4,nat_at_type))
                   (@valid_const nat nil nat 4 (@erefl Type nat))
                   (@valid_var nat [:: (4,nat_at_type)] 4 _)).

Definition example : Rml :=
  (If_stm (Const bool true)
          (Let_stm
             (16,bool_at_type) (Const bool true)
             (Let_stm
                (12,nat_at_type) (Const nat_at_type 4)
                (If_stm (Var (16,bool_at_type)) (Var (12,nat_at_type)) (Const nat 10))))
          (Const nat 900)).

Lemma ez1 : List.In (16, bool_at_type) [:: (12, nat_at_type); (16, bool_at_type)].
  simpl.
  right.
  left.
  reflexivity.
Qed.

Lemma ez2 : List.In (12, nat_at_type) [:: (12, nat_at_type); (16, bool_at_type)].
  left.
  reflexivity.
Qed.

Definition example_valid : rml_valid_type nat_at_type nil example :=
  @valid_if nat_at_type nil
            (Const bool_at_type true)
            (Let_stm (16,bool_at_type)
                     (Const bool_at_type true)
                     (Let_stm (12,nat_at_type)
                              (Const nat_at_type 4)
                              (If_stm (Var (16,bool_at_type))
                                      (Var (12,nat_at_type))
                                      (Const nat_at_type 10))))
            (Const nat_at_type 900)
            
   (@valid_const bool_at_type nil bool_at_type true (@erefl Type bool_at_type) )
            (valid_let nat_at_type nil bool_at_type 16
                       (Const bool_at_type true)
                       (Let_stm (12,nat_at_type)
                                (Const nat_at_type 4)
                                (If_stm (Var (16,bool_at_type))
                                        (Var (12,nat_at_type))
                                        (Const nat_at_type 10)))
                       
            (@valid_const bool_at_type nil bool_at_type true (@erefl Type bool_at_type))
            (valid_let nat_at_type [:: (16,bool_at_type)] nat_at_type 12
                       (Const nat_at_type 4)
                       (If_stm (Var (16,bool_at_type))
                               (Var (12,nat_at_type))
                               (Const nat_at_type 10))
            (@valid_const nat_at_type [:: (16,bool_at_type)] nat_at_type 4 (@erefl Type nat))
            (valid_if nat_at_type [:: (12,nat_at_type) ; (16,bool_at_type)]
                      (Var (16,bool_at_type))
                      (Var (12,nat_at_type))
                      (Const nat_at_type 10)
              (valid_var bool_at_type [:: (12,nat_at_type) ; (16,bool_at_type)] 16 ez1)
              (valid_var nat_at_type [:: (12,nat_at_type) ; (16,bool_at_type)] 12 ez2)
              (@valid_const nat_at_type [:: (12,nat_at_type) ; (16,bool_at_type)] nat_at_type 10 (@erefl Type nat_at_type)))))
            (@valid_const nat_at_type nil nat_at_type 900 (@erefl Type nat)).

Check @interp_rml.
Check @interp_rml nat_at_type example nat example_valid id.
Compute @interp_rml nat_at_type example nat example_valid id.

Example ie1 :
  @interp_rml nat_at_type example nat example_valid id = 4.
Proof.
  simpl.
Admitted.

Compute interp_rml example _ example_valid.

(* -------------------------------------------------------------------------------- *)

Compute @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil).

Compute @interp_rml _ (Let_stm (12,_) (@Const nat 4) (Var (12,_))) nat (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat _)).

Example const_4_interp :
  forall R Q, @interp_rml R (Let_stm (12,_) (@Const nat 4) (Var (12,_))) nat (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil (@valid_const nat nat 4 (@erefl Type nat) nil) (@valid_var 12 [:: (12, _)] nat Q)) = @interp_rml _ (Const nat 4) _ (@valid_const nat nat 4 (@erefl Type nat) nil).
Proof.
  simpl.
  intros.
  unfold replace_all_variables_type.
  simpl.
  destruct boolp.pselect.
  simpl.
Admitted.

(** **)


Definition example_a := (@Const nat 4).
Definition example_b := (Var (12,nat_at_type)).
Definition example_let := (Let_stm (12,nat_at_type) example_a example_b).

Definition valid_a := (@valid_const nat nat 4 (@erefl Type nat) nil).
Check valid_a.
Definition valid_b : rml_valid_type nat example_b [:: (12, nat_at_type)].
Proof.
  refine (@valid_var 12 [:: (12, nat_at_type)] nat _).
  simpl.
  left.
  reflexivity.
Defined.
  
Definition valid_let' := (@valid_let nat nat 12 (@Const nat 4) (Var (12,_)) nil valid_a valid_b).

Compute @interp_rml _ example_let nat valid_let'.

Definition example_function := (fix contains_zero l :=
                                  match l with
                                  | nil => false
                                  | x :: xs => if x == 0
                                             then true
                                             else contains_zero xs end).
Definition example_list := 2 :: 3 :: 0 :: 4 :: 8 :: nil.

Definition example_e1 := (Const (list nat -> bool) example_function).
Definition example_e2 := (Const (list nat) example_list).

Definition example_valid1 := (@valid_const (list nat -> bool) (list nat -> bool) (example_function) (@erefl Type (list nat -> bool)) nil).
Definition example_valid2 := (@valid_const (list nat) (list nat) (example_list) (@erefl Type (list nat)) nil).

Compute @interp_rml _ (App_stm (list nat) example_e1 example_e2) bool (@valid_app bool (list nat) example_e1 example_e2 nil example_valid1 example_valid2).

Example translate_exp_cst :
    forall n p, translate_pWhile_expr_to_rml (cst_ n) (initial_env p) = Const nat n.
Proof.
  intros.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.

Example translate_exp_var :
    forall T x n p, translate_pWhile_expr_to_rml (var_ x) (@extend_env (@vname _ T x) n (initial_env p)) = Var n.
Proof.
  intros.
  simpl.
  destruct n.
  - simpl.
    case (pselect _).
    + intros.
      simpl.
      reflexivity.
    + intros.
      easy.
Qed.


Example translate_cmd_example1 :
  forall (T : Type) x (n1 n2 : nat),
    T = nat ->
    translate_pWhile_cmd_to_rml
      (seqc (assign x (cst_ n1)) (assign x (cst_ n2))) x (@initial_env (0,T))
    = Let_stm (0,T) (Const nat n1) (Let_stm (0,T) (Const nat n2) (Var (0,T))).
Proof.
  intros.
  subst.
  simpl.
  unfold initial_env.
  reflexivity.
Qed.

Compute (fun x => translate_pWhile_cmd_to_rml (seqc (assign x (cst_ 4)) (assign x (cst_ 6))) x (@initial_env (0,_))).

(* translate_pWhile_cmd_to_rml (seqc (skip) (assign x (cst_ n))) x (@initial_env (0,T))) *)

Definition nat2 : Type := nat.
Example H0 :
  (forall (n : nat) (A : Type)
           (t : List.In (n, A) [seq i.1 | i <- [:: (4, nat2, Const nat 4)]]),
         rml_valid_type A (lookup_in [:: (4, nat2, Const nat 4)] (n, A) t)
                        [seq i.1 | i <- [:: (4, nat2, Const nat 4)]]).
Proof.
  intros.
    simpl.
    inversion t ; subst.
    inversion H.
    + destruct pselect.
      * simpl in *.
        destruct e.
        simpl.
        constructor.
        rewrite <- H2.
        reflexivity.
      * contradiction.
    + contradiction.
Defined.

Example H1 : (List.In (4, nat2) [seq i.1 | i <- [:: (4, nat2, Const nat 4)]]).
Proof.
  simpl.
  left.
  reflexivity.
Defined.

Compute (lookup [:: (4, nat2, (Const nat 4))] (4,nat2) H0 H1).
Example look :
  (lookup [:: (4, nat2, (Const nat 4))] (4,nat2) H0 H1) = (Const nat 4).
Proof.
  simpl.
  destruct pselect.
  -- reflexivity.
  -- contradiction.
Qed.
