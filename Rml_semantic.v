From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Require Import Rml.

From xhl Require Import pwhile.pwhile.
From xhl Require Import pwhile.psemantic.

Require Import Util.

(* -------------------------------------------------------------------------------- *)

Check 5 \in [:: 2 ; 3 ; 4 ; 5] = true.

Fixpoint lookup {R} (env : seq (nat * Type * (forall A : Type, continuation_monad_type R A)))
         (p : nat * Type) `{_ : List.In p (map fst env)} {struct env} : (forall A : Type, continuation_monad_type R A).
Proof.
  induction env.
  - contradiction.
  - simpl in H.
    destruct (pselect (a.1 = p)).
    + exact a.2.
    + assert (List.In p [seq i.1 | i <- env]) by (inversion H ; easy).
      intros.
      apply IHenv with (A := A) in H0.
      assumption.
Qed.

(* . *)
(*   destruct x ; intros. *)
(*   - assert (List.In p (map fst fun_env)) by (inversion x_valid ; easy). *)
(*     apply (@lookup R fun_env p H). *)
(*   - exact (unit a). *)
(*   - assert (fun_valid : srml_valid_type A (p :: [ seq i.1 | i <- fun_env]) x) by (inversion x_valid ; assumption). *)

(*     pose (fun (t : A) => interp_srml_aux A R x ((p,t) :: fun_env) fun_valid). *)
(*     pose (fun (t : A) => interp_srml_aux A R x ((p,t) :: fun_env) fun_valid). *)
(*     pose (fun (f : (A -> continuation_monad_type R A)) => f c). *)
(*     exact . *)
(*     exact (c). *)
(*   - exact ((interp_srml b) >>= (fun (t : bool) => if t then (interp_srml m1) else (interp_srml m2))). *)
  

Fixpoint interp_srml_aux {A} {R} (x : @sRml A) (fun_env : seq (nat * Type * (forall A, continuation_monad_type R A))) `{x_valid : srml_valid_type A (map fst fun_env) x} : continuation_monad_type R A.
  destruct x.
  - refine (@lookup R fun_env p _ A).
    inversion x_valid ; subst.
    assumption.
  - refine (unit a).
  - refine (interp_srml_aux A R x fun_env _).
    inversion x_valid.
  - assert (srml_valid_type bool [seq i.1 | i <- fun_env] x1 /\ srml_valid_type A [seq i.1 | i <- fun_env] x2 /\ srml_valid_type A [seq i.1 | i <- fun_env] x3) by (inversion x_valid ; subst ; easy).
    inversion_clear H as [H1 [H2 H3]].
    
    exact ((interp_srml_aux bool R x1 fun_env H1) >>= (fun (t : bool) => if t then (interp_srml_aux A R x2 fun_env H2) else (interp_srml_aux A R x3 fun_env H3))).
  - assert (srml_valid_type (T -> A) [seq i.1 | i <- fun_env] x1 /\ srml_valid_type T [seq i.1 | i <- fun_env] x2).
    apply helper in x_valid.
    inversion x_valid ; subst ; easy.

    inversion_clear H.
    
    exact ((interp_srml_aux (T -> A) R x1 fun_env H0) >>= (fun (g : T -> A) => (interp_srml_aux T R x2 fun_env H1) >>= (fun k => unit (g k)))).

  - assert (srml_valid_type p.2 (p0 :: p :: [seq i.1 | i <- fun_env]) x1 /\ srml_valid_type (p.2 -> A) (p :: [seq i.1 | i <- fun_env]) x2) by (inversion x_valid ; subst ; clear a b H1 H2 ; apply helper2 in x_valid ; inversion x_valid ; subst ; easy).
    inversion_clear H.

    (* TODO USE THAT IT IS omega-CPO *)
    
    exact ((interp_srml_aux (p.2 -> A) R x2 ((p,x2) :: fun_env) H1) >>= (fun g => (interp_srml_aux p.2 R x1 ((p0,_) :: (p,_) :: fun_env) H0) >>= (fun t => unit (g t)))).
Defined.

Compute interp_srml_aux (sFix (0,nat <: Type) (1,nat <: Type) (sConst 2) (sFun (1,nat <: Type) (sVar (1,nat <: Type)))) nil (valid_fix).
  
  (* match x with *)
  (* | sVar p => @lookup R fun_env p (@H A R p fun_env x_valid) A *)
  (* | sConst c => unit c *)
  (* | sFun p x => interp_srml_aux x fun_env (* TODO *) *)
  (* | sIf b m1 m2 => (interp_srml_aux b fun_env) >>= (fun (t : bool) => if t then (interp_srml_aux m1 fun_env) else (interp_srml_aux m2 fun_env)) *)
  (* | sApp C e1 e2 => (interp_srml_aux e1 fun_env) >>= (fun (g : C -> A) => (interp_srml_aux e2 fun_env) >>= (fun k => unit (g k))) *)
  (* | sFix B C f k => (interp_srml_aux k fun_env) >>= (fun g => (interp_srml_aux f fun_env) >>= (fun t => unit (g t))) (* TODO *) *)
  (* end *)


(* -------------------------------------------------------------------------------- *)

Fixpoint interp_rml {R} (x : Rml) {A} `{x_valid : rml_valid_type A nil x} : continuation_monad_type R A := interp_srml (@replace_all_variables_type A x x_valid).

(* -------------------------------------------------------------------- *)

Fixpoint interp_rml' {R} (x : Rml) {A} : option (continuation_monad_type R A) :=
  compute_valid A nil x >>= (fun x_valid =>
  Some (interp_srml (@replace_all_variables_type A x x_valid))).

(* -------------------------------------------------------------------- *)

Definition Choice T := (ChoiceType (EqType T gen_eqMixin) gen_choiceMixin).

Lemma choice_of_type_to_choice_type :
  forall {R : realType} (x : distr R (Choice bool)), distr R (bool_choiceType).
Proof.
Admitted.

Fixpoint ubn {R : realType} {A : choiceType} (f : A -> distr R A) t n := fun a =>
  if n is n.+1 return distr R A then
    if t a then \dlet_(x <- f a) @ubn R A f t n x else @dunit R A a
  else dnull.

Fixpoint ssem_aux {R : realType} {T : Type} (x : @sRml T) : {distr (Choice T) / R} :=
  match x with
  | sConst c => @dunit R (Choice T) c
  | sIf_stm b m1 m2 =>
    let b'' := choice_of_type_to_choice_type (ssem_aux b) in
    \dlet_(b' <- b'') (if b' then ssem_aux m1 else ssem_aux m2)

  | sApp_stm A e1 e2 =>
    @dlet R (Choice (A -> T)) (Choice T) (fun t =>
    @dlet R (Choice A) (Choice T) (fun u =>
    @dunit R (Choice T) (t u)) (@ssem_aux R A e2)) (ssem_aux e1)

  | sFix A B f k =>
    dlim (fun n => ubn (fun a => ssem_aux k) (ssem_aux f) n)
    
    (* @dlet R (Choice (((A -> B) -> A -> B) -> T)) (Choice T) (fun t => *)
    (* @dlet R (Choice ((A -> B) -> A -> B)) (Choice T) (fun u => *)
    (* @dunit R (Choice T) (t u)) (ssem_aux f)) (ssem_aux k) *)
    (* TODO Use @dlim instead *)          
  end.

Fixpoint ssem {R : realType} {T : Type} (x : Rml) `{x_valid : rml_valid_type T nil x} : {distr (Choice T) / R} :=
  let y := @replace_all_variables_type T x x_valid in
  @ssem_aux R T y.