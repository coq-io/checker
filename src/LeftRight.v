Require Import Io.All.

Inductive t (E : Effect.t) : Type -> Type :=
| Ret : forall A, A -> t E A
| Call : forall c, t E (Effect.answer E c)
| Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
| Choose : forall (A : Type), t E A -> t E A -> t E A
| JoinLeft : forall (A B : Type), t E A -> t E B -> t E (A * B)
| JoinRight : forall (A B : Type), t E A -> t E B -> t E (A * B).
Arguments Ret {E A} _.
Arguments Call {E} _.
Arguments Let {E A B} _ _.
Arguments Choose {E A} _ _.
Arguments JoinLeft {E A B} _ _.
Arguments JoinRight {E A B} _ _.

Definition join {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  Choose (JoinLeft x y) (JoinRight x y).

Module LastStep.
  Inductive t {E : Effect.t} : forall {A}, LeftRight.t E A -> A -> Type :=
  | Ret : forall A (v : A),
    t (LeftRight.Ret v) v
  | Let : forall A B (x : LeftRight.t E A) (f : A -> LeftRight.t E B) v_x v_y,
    t x v_x -> t (f v_x) v_y ->
    t (LeftRight.Let x f) v_y
  | ChooseLeft : forall A (x1 x2 : LeftRight.t E A) v,
    t x1 v ->
    t (LeftRight.Choose x1 x2) v
  | ChooseRight : forall A (x1 x2 : LeftRight.t E A) v,
    t x2 v ->
    t (LeftRight.Choose x1 x2) v
  | JoinLeft : forall A B (x : LeftRight.t E A) v_x (y : LeftRight.t E B) v_y,
    t x v_x -> t y v_y ->
    t (LeftRight.JoinLeft x y) (v_x, v_y)
  | JoinRight : forall A B (x : LeftRight.t E A) v_x (y : LeftRight.t E B) v_y,
    t x v_x -> t y v_y ->
    t (LeftRight.JoinRight x y) (v_x, v_y).
End LastStep.

Module Step.
  Inductive t {E : Effect.t}
    : forall {A}, LeftRight.t E A -> LeftRight.t E A -> Type :=
  | Call : forall c a, t (LeftRight.Call c) (LeftRight.Ret a)
  | Let : forall A B (x x' : LeftRight.t E A) (f : A -> LeftRight.t E B),
    t x x' ->
    t (LeftRight.Let x f) (LeftRight.Let x' f)
  | LetDone : forall A B (x : LeftRight.t E A) (v : A) (f : A -> LeftRight.t E B) (y : LeftRight.t E B),
    LastStep.t x v -> t (f v) y ->
    t (LeftRight.Let x f) y
  | ChooseLeft : forall A (x1 x2 x1' : LeftRight.t E A),
    t x1 x1' ->
    t (LeftRight.Choose x1 x2) x1'
  | ChooseRight : forall A (x1 x2 x2' : LeftRight.t E A),
    t x2 x2' ->
    t (LeftRight.Choose x1 x2) x2'
  | JoinLeft : forall A B (x x' : LeftRight.t E A) (y : LeftRight.t E B),
    t x x' ->
    t (LeftRight.JoinLeft x y) (LeftRight.join x' y)
  | JoinRight : forall A B (x : LeftRight.t E A) (y y' : LeftRight.t E B),
    t y y' ->
    t (LeftRight.JoinRight x y) (LeftRight.join x y').
End Step.

Fixpoint compile {E A} (x : C.t E A) : t E A :=
  match x with
  | C.Ret _ v => Ret v
  | C.Call c => Call c
  | C.Let _ _ x f => Let (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => Choose (compile x1) (compile x2)
  | C.Join _ _ x y => join (compile x) (compile y)
  end.
