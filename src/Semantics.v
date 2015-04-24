Require Import Io.All.
Require Choose.

Module C.
  Module Last.
    Module Path.
      Inductive t : Set :=
      | Ret : t
      | Let : t -> t -> t
      | ChooseLeft : t -> t
      | ChooseRight : t -> t
      | Join : t -> t -> t.
    End Path.

    Module Eval.
      Inductive t {E : Effect.t}
        : forall {A : Type}, Path.t -> C.t E A -> A -> Prop :=
      | Ret : forall A (v : A), t Path.Ret (C.Ret E v) v
      | Let : forall A B p_x x v_x p_f f v_f,
        t p_x x v_x -> t p_f (f v_x) v_f ->
        t (Path.Let p_x p_f) (C.Let A B x f) v_f
      | ChooseLeft : forall A p_x1 x1 v_x1 x2,
        t p_x1 x1 v_x1 -> t (Path.ChooseLeft p_x1) (C.Choose A x1 x2) v_x1
      | ChooseRight : forall A x1 p_x2 x2 v_x2,
        t p_x2 x2 v_x2 -> t (Path.ChooseRight p_x2) (C.Choose A x1 x2) v_x2
      | Join : forall A B p_x x v_x p_y y v_y,
        t p_x x v_x -> t p_y y v_y ->
        t (Path.Join p_x p_y) (C.Join A B x y) (v_x, v_y).
    End Eval.
  End Last.

  Module Path.
    Inductive t : Set :=
    | Call : t
    | Let : t -> t
    | LetDone : Last.Path.t -> t -> t
    | ChooseLeft : t -> t
    | ChooseRight : t -> t
    | JoinLeft : t -> t
    | JoinRight : t -> t.
  End Path.

  Module Eval.
    Inductive t {E : Effect.t} (c : Effect.command E) (a : Effect.answer E c)
      : forall {A : Type}, Path.t -> C.t E A -> C.t E A -> Prop :=
    | Call : t c a Path.Call (C.Call c) (C.Ret E a)
    | Let : forall A B p_x x x' f,
      t c a p_x x x' -> t c a (Path.Let p_x) (C.Let A B x f) (C.Let A B x' f)
    | LetDone : forall A B p_x x v_x p_f f f',
      Last.Eval.t p_x x v_x -> t c a p_f (f v_x) f' ->
      t c a (Path.LetDone p_x p_f) (C.Let A B x f) f'
    | ChooseLeft : forall A p_x1 x1 x1' x2,
      t c a p_x1 x1 x1' ->
      t c a (Path.ChooseLeft p_x1) (C.Choose A x1 x2) x1'
    | ChooseRight : forall A x1 p_x2 x2 x2',
      t c a p_x2 x2 x2' ->
      t c a (Path.ChooseRight p_x2) (C.Choose A x1 x2) x2'
    | JoinLeft : forall A B p_x x x' y,
      t c a p_x x x' ->
      t c a (Path.JoinLeft p_x) (C.Join A B x y) (C.Join A B x' y)
    | JoinRight : forall A B x p_y y y',
      t c a p_y y y' ->
      t c a (Path.JoinRight p_y) (C.Join A B x y) (C.Join A B x y').
  End Eval.
End C.

Module Choose.
  Module Path.
    Inductive t : Set :=
    | Done : t
    | ChooseLeft : t -> t
    | ChooseRight : t -> t.

    Fixpoint bind (p_x p_f : t) : t :=
      match p_x with
      | Done => p_f
      | ChooseLeft p_x => ChooseLeft (bind p_x p_f)
      | ChooseRight p_x => ChooseRight (bind p_x p_f)
      end.

    Fixpoint bind_assoc (p_x p_y p_z : t)
      : bind p_x (bind p_y p_z) = bind (bind p_x p_y) p_z.
      destruct p_x; simpl.
      - reflexivity.
      - now rewrite bind_assoc.
      - now rewrite bind_assoc.
    Qed.

    Definition join (p_x p_f : t) : t :=
      ChooseLeft (bind p_x p_f).
  End Path.

  Module Last.
    Module Eval.
      Inductive t {E : Effect.t} {A : Type}
        : Path.t -> Choose.t E A -> A -> Prop :=
      | Ret : forall v, t Path.Done (Choose.Ret v) v
      | ChooseLeft : forall p_x1 x1 x2 v,
        t p_x1 x1 v -> t (Path.ChooseLeft p_x1) (Choose.Choose x1 x2) v
      | ChooseRight : forall p_x2 x1 x2 v,
        t p_x2 x2 v -> t (Path.ChooseRight p_x2) (Choose.Choose x1 x2) v.
      End Eval.
  End Last.

  Module Eval.
    Inductive t {E : Effect.t} (c : Effect.command E) (a : Effect.answer E c)
      {A : Type} : Path.t -> Choose.t E A -> Choose.t E A -> Prop :=
    | Call : forall h, t c a Path.Done (Choose.Call c h) (h a)
    | ChooseLeft : forall p_x1 x1 x2 x1',
      t c a p_x1 x1 x1' ->
      t c a (Path.ChooseLeft p_x1) (Choose.Choose x1 x2) x1'
    | ChooseRight : forall p_x2 x1 x2 x2',
      t c a p_x2 x2 x2' ->
      t c a (Path.ChooseRight p_x2) (Choose.Choose x1 x2) x2'.
  End Eval.
End Choose.
