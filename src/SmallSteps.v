Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> Prop;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.

Module C.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Join : forall {B C : Type}, t E B -> t E C -> (B * C -> t E A) -> t E A
  | Choose : t E A -> t E A -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Join {E A B C} _ _ _.
  Arguments Choose {E A} _ _.

  Module Step.
    Inductive t {E : Effect.t} {A : Type} (c : Effect.command E)
      (a : Effect.answer E c) : C.t E A -> C.t E A -> Type :=
    | Call : forall h,
      t c a (C.Call c h) (h a)
    | JoinLeft : forall B C (x : C.t E B) (y : C.t E C) h x',
      t c a (A := B) x x' ->
      t c a (C.Join x y h) (C.Join x' y h)
    | JoinRight : forall B C (x : C.t E B) (y : C.t E C) h y',
      t c a (A := C) y y' ->
      t c a (C.Join x y h) (C.Join x y' h)
    | Join : forall B C (x : B) (y : C) h,
      t c a (C.Join (C.Ret x) (C.Ret y) h) (h (x, y))
    | ChooseLeft : forall x1 x2 x1',
      t c a x1 x1' ->
      t c a (C.Choose x1 x2) x1'
    | ChooseRight : forall x1 x2 x2',
      t c a x2 x2' ->
      t c a (C.Choose x1 x2) x2'.
  End Step.

  Module ModelStep.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type} (s : S)
      : C.t E A -> S -> C.t E A -> Type :=
    | Call : forall c h,
      Model.condition m c s ->
      t m s (C.Call c h) (Model.state m c s) (h (Model.answer m c s))
    | JoinLeft : forall B C (x : C.t E B) (y : C.t E C) h s' x',
      t m (A := B) s x s' x' ->
      t m s (C.Join x y h) s' (C.Join x' y h)
    | JoinRight : forall B C (x : C.t E B) (y : C.t E C) h s' y',
      t m (A := C) s y s' y' ->
      t m s (C.Join x y h) s' (C.Join x y' h)
    | Join : forall B C (x : B) (y : C) h,
      t m s (C.Join (C.Ret x) (C.Ret y) h) s (h (x, y))
    | ChooseLeft : forall x1 x2 s' x1',
      t m s x1 s' x1' ->
      t m s (C.Choose x1 x2) s' x1'
    | ChooseRight : forall x1 x2 s' x2',
      t m s x2 s' x2' ->
      t m s (C.Choose x1 x2) s' x2'.
  End ModelStep.
End C.
