
(* M A = (A -> distr R A) -> distr R A *)
(* t -> Mt *)
Definition unit {R : realType} {A : choiceType} : A -> (A -> distr R A) -> distr R A :=
  (fun x => (fun f => f x)).

(* Mt -> (t -> Ms) -> Ms *)
Definition bind {R} {A B : choiceType}
  : ((A -> distr R A) -> distr R A) -> (A -> (B -> distr R B) -> distr R B) -> (B -> distr R B) -> distr R B :=
  fun x => fun f => fun g => dlet (fun v => f v g) (x (@dunit R A)).

Theorem bind_unit :
  forall R A B,
  forall x M y,
    @bind R A B (unit x) M y =1 M x y.
Proof.
  unfold "=1".
  intros.
  apply (@dlet_unit R A B (fun x => M x y) x).
Qed.

Theorem bind_bind :
  forall R A B,
  forall mu M1 M2 y,
    @bind R A B (bind mu M1) M2 y =1 @bind R A B mu (fun x => bind (M1 x) M2) y.
Proof.
  intros.
  apply dlet_dlet.
Qed.

Theorem bind_unit_id :
  forall R A,
  forall mu,
    @bind R A A mu (@unit R A) (@dunit R A) =1 mu (@dunit R A). (* TODO: make it work for any distribution *)
Proof.
  intros.
  unfold bind.
  unfold unit.
  apply dlet_dunit_id.
Qed.


Inductive Rml {R : realType} {A : choiceType} :=
| Var : nat_choiceType -> Rml          
| Const : A -> @Rml R A
| Let_stm : nat_choiceType -> Rml -> Rml -> Rml
| Fun_stm : nat_choiceType -> choiceType -> Rml -> Rml
| If_stm : (@Rml R bool_choiceType) -> Rml -> Rml -> Rml
| App_stm : Rml -> Rml -> Rml.

Definition Mif {R B} (mu_b : (bool_choiceType -> distr R bool_choiceType) -> distr R bool_choiceType) mu1 mu2 :=
  @bind R bool_choiceType B mu_b (fun b => if b then mu1 else mu2).

(* Convert to continuations *)
Fixpoint interp {R : realType} {A : choiceType} (x : @Rml R A) (l : seq (nat_choiceType * A)) :
  (A -> distr R A) -> distr R A.
Proof.
  case x ; clear x.
  - intros s.
    refine 
       (fun x => (fix let_rec l :=
          match l with
          | nil => dnull
          | (s',v) :: r =>
            if s == s'
            then @unit R A v x
            else (fun x => let_rec r) x
          end) l).
  - intros v.
    refine (fun x => @unit R A v x).
  - intros x a b.
    refine (@bind R A A (@interp R A a l) (fun v => @interp R A b ((x, v) :: l))).
  - intros x sigma t.
    Check unit.
    Check unit (fun x => x).
    
    refine (fun g => @interp R A t l (fun v => g v)).
Defined.
    
Fixpoint interp {R : realType} {A : choiceType} (x : @Rml R A) (l : seq (nat_choiceType * A)) :
  (A -> distr R A) -> distr R A :=
  match x with
  | Var s =>
    (fun x =>
       (fix let_rec l :=
          match l with
          | nil => dnull
          | (s',v) :: r =>
            if s == s'
            then @unit R A v x
            else (fun x => let_rec r) x
          end) l)
  | Const v => (fun x => @unit R A v x)
  | Let_stm x a b => @bind R A A (interp a l) (fun v => interp b ((x, v) :: l))
  | Fun_stm x sigma t => (fun g => interp t l (fun v => g v))
  | If_stm b a1 a2 => Mif (interp b nil) (interp a1 l) (interp a2 l)
  | App_stm e1 e2 => bind (interp e2 l) (fun v => interp e1 ((0%nat,v) :: l)) (* Todo: replace 0 with correct index *)
  end.
