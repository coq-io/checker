Require Import Io.All.

Inductive t (E : Effect.t) (A : Type) : Type :=
| Ret : A -> t E A
| Call : forall c, (Effect.answer E c -> t E A) -> t E A
| Choose : t E A -> t E A -> t E A.
Arguments Ret {E A} _.
Arguments Call {E A} _ _.
Arguments Choose {E A} _ _.

Module Last.
  Module Path.
    Inductive t : Set :=
    | Ret : t
    | ChooseLeft : t -> t
    | ChooseRight : t -> t.

    Module Eval.
      Inductive t {E : Effect.t} {A : Type}
        : Path.t -> Choose.t E A -> A -> Prop :=
      | Ret : forall v, t Path.Ret (Choose.Ret v) v
      | ChooseLeft : forall p_x1 x1 x2 v,
        t p_x1 x1 v -> t (ChooseLeft p_x1) (Choose.Choose x1 x2) v
      | ChooseRight : forall p_x2 x1 x2 v,
        t p_x2 x2 v -> t (ChooseRight p_x2) (Choose.Choose x1 x2) v.
    End Eval.
  End Path.
End Last.

Module Path.
  Inductive t : Set :=
  | Call : t
  | ChooseLeft : t -> t
  | ChooseRight : t -> t.

  Module Eval.
    Inductive t {E : Effect.t} {c : Effect.command E} (a : Effect.answer E c)
      {A : Type} : Path.t -> Choose.t E A -> Choose.t E A -> Prop :=
    | Call : forall h, t a Path.Call (Choose.Call c h) (h a)
    | ChooseLeft : forall p_x1 x1 x2 v,
      t a p_x1 x1 v -> t a (Path.ChooseLeft p_x1) (Choose.Choose x1 x2) v
    | ChooseRight : forall p_x2 x1 x2 v,
      t a p_x2 x2 v -> t a (Path.ChooseRight p_x2) (Choose.Choose x1 x2) v.
  End Eval.
End Path.

Fixpoint map {E A B} (x : t E A) (f : A -> B) : t E B :=
  match x with
  | Ret v => Ret (f v)
  | Call c h => Call c (fun a => map (h a) f)
  | Choose x1 x2 => Choose (map x1 f) (map x2 f)
  end.

Fixpoint bind {E A B} (x : t E A) (f : A -> t E B) : t E B :=
  match x with
  | Ret v => f v
  | Call c h => Call c (fun a => bind (h a) f)
  | Choose x1 x2 => Choose (bind x1 f) (bind x2 f)
  end.

Fixpoint join_left_aux {E A B} (x : t E A) (y : t E B)
  (join_right : forall A, t E A -> t E (A * B)) : t E (A * B) :=
  match x with
  | Ret v => map y (fun y => (v, y))
  | Call c h => Call c (fun a => Choose (join_left_aux (h a) y join_right) (join_right _ (h a)))
  | Choose x1 x2 => Choose (join_left_aux x1 y join_right) (join_left_aux x2 y join_right)
  end.

Fixpoint join_right {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  match y with
  | Ret v => map x (fun x => (x, v))
  | Call c h => Call c (fun a => Choose (join_left_aux x (h a) (fun _ x => join_right x (h a))) (join_right x (h a)))
  | Choose y1 y2 => Choose (join_right x y1) (join_right x y2)
  end.

Definition join_left {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  join_left_aux x y (fun _ x => join_right x y).

Definition join {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  Choose (join_left x y) (join_right x y).
