From xhl Require Import pwhile.pwhile.
From xhl Require Import inhabited notations.

Require Import Rml.

Fixpoint translate_pWhile_to_rml (x : cmd)  : Rml :=
  match x with
  | abort => 
  end.
  
  