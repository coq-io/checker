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

Module Compile.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> LeftRight.t E A -> Type :=
  | Ret : forall A (v : A), t (C.Ret _ v) (LeftRight.Ret v)
  | Call : forall c, t (C.Call c) (LeftRight.Call c)
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B) c_x c_f,
    t x c_x -> (forall v_x, t (f v_x) (c_f v_x)) ->
    t (C.Let _ _ x f) (LeftRight.Let c_x c_f)
  | Choose : forall A (x1 x2 : C.t E A) c_x1 c_x2,
    t x1 c_x1 -> t x2 c_x2 ->
    t (C.Choose _ x1 x2) (LeftRight.Choose c_x1 c_x2)
  | Join : forall A B (x : C.t E A) (y : C.t E B) c_x c_y,
    t x c_x -> t y c_y ->
    t (C.Join _ _ x y) (LeftRight.join c_x c_y).

  Fixpoint compile {E A} (x : C.t E A) : LeftRight.t E A :=
    match x with
    | C.Ret _ v => LeftRight.Ret v
    | C.Call c => LeftRight.Call c
    | C.Let _ _ x f => LeftRight.Let (compile x) (fun x => compile (f x))
    | C.Choose _ x1 x2 => LeftRight.Choose (compile x1) (compile x2)
    | C.Join _ _ x y => LeftRight.join (compile x) (compile y)
    end.

  Fixpoint make {E A} (x : C.t E A) : t x (compile x).
    destruct x.
    - apply Ret.
    - apply Call.
    - now apply Let.
    - now apply Choose.
    - now apply Join.
  Defined.
End Compile.

Module Sound.

End Sound.
