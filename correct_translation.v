From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets reals distr.

Require Import Rml.
Require Import Rml_semantic.
Require Import pWhileInterp.

From xhl Require Import pwhile.pwhile.
From xhl Require Import pwhile.psemantic.

Compute @translate_pWhile_expr_to_rml nat (cst_ 4) (initial_env _).
Compute @Rml_semantic.ssem pwhile.R _ (Rml.Const nat 4) (@valid_const nat nat 4 (erefl) nil).
Check Rml_semantic.ssem (@translate_pWhile_expr_to_rml nat (cst_ 4) (initial_env _)).

Theorem commuting_translations_expr :
  forall (e : expr (pwhile.R)) (env : ident -> nat * Type) (x_valid : rml_valid_type (pwhile.R) (translate_pWhile_expr_to_rml e env) [::]) (val : Choice (pwhile.R)) (mem : cmem),
    @Rml_semantic.ssem pwhile.R _ (@translate_pWhile_expr_to_rml (pwhile.R) e env) x_valid val = esem e mem.
Proof.
  simpl.
  intros.
  
Qed.
  
Theorem commuting_translations :
  forall T (k : inhabited.Inhabited.type) cmd ret env mem x_valid val,
    @Rml_semantic.ssem _ T (@translate_pWhile_cmd_to_rml cmd k ret env) x_valid val = ssem cmd mem mem.
Proof.
  induction cmd ; intros.
  - 
  
  intros.
  unfold ssem.
  unfold Rml_semantic.ssem.
  
  