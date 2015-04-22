Require Import Io.All.
Require Choose.

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
  Inductive t {E : Effect.t} {c : Effect.command E} (a : Effect.answer E c)
    : forall {A : Type}, Path.t -> C.t E A -> C.t E A -> Prop :=
  | Call : t a Path.Call (C.Call c) (C.Ret E a)
  | Let : forall A B p_x x x' f,
    t a p_x x x' -> t a (Path.Let p_x) (C.Let A B x f) (C.Let A B x' f)
  | LetDone : forall A B p_x x v_x p_f f f',
    Last.Eval.t p_x x v_x -> t a p_f (f v_x) f' ->
    t a (Path.LetDone p_x p_f) (C.Let A B x f) f'
  | ChooseLeft : forall A p_x1 x1 x1' x2,
    t a p_x1 x1 x1' ->
    t a (Path.ChooseLeft p_x1) (C.Choose A x1 x2) (C.Choose A x1' x2)
  | ChooseRight : forall A x1 p_x2 x2 x2',
    t a p_x2 x2 x2' ->
    t a (Path.ChooseRight p_x2) (C.Choose A x1 x2) (C.Choose A x1 x2')
  | JoinLeft : forall A B p_x x x' y,
    t a p_x x x' ->
    t a (Path.JoinLeft p_x) (C.Join A B x y) (C.Join A B x' y)
  | JoinRight : forall A B x p_y y y',
    t a p_y y y' ->
    t a (Path.JoinRight p_y) (C.Join A B x y) (C.Join A B x y').
End Eval.

(*Module Step.
  Inductive t {E : Effect.t} (c : Effect.command E) : Type -> Type :=
  | Call : Effect.answer E c -> t c (Effect.answer E c)
  | Let : forall A B,
    t c A -> (A -> C.t E B) -> t c B
  | LetDone : forall A B (x : C.t E A) (v : A),
    LastStep.t x v -> (A -> C.t E B) -> t c B -> t c B
  | ChooseLeft : forall A,
    t c A -> C.t E A -> t c A
  | ChooseRight : forall A,
    C.t E A -> t c A -> t c A
  | JoinLeft : forall A B,
    t c A -> C.t E B -> t c (A * B)
  | JoinRight : forall A B,
    C.t E A -> t c B -> t c (A * B).

  Fixpoint start {E c A} (step : t c A) : C.t E A :=
    match step with
    | Call _ => C.Call c
    | Let _ _ step_x f => C.Let _ _ (start step_x) f
    | LetDone _ _ x _ _ f _ => C.Let _ _ x f
    | ChooseLeft _ step_x1 x2 => C.Choose _ (start step_x1) x2
    | ChooseRight _ x1 step_x2 => C.Choose _ x1 (start step_x2)
    | JoinLeft _ _ step_x1 x2 => C.Join _ _ (start step_x1) x2
    | JoinRight _ _ x1 step_x2 => C.Join _ _ x1 (start step_x2)
    end.

  Fixpoint answer {E c A} (step : t c A) : Effect.answer E c :=
    match step with
    | Call a => a
    | Let _ _ step_x _ => answer step_x
    | LetDone _ _ _ _ _ _ step_f => answer step_f
    | ChooseLeft _ step_x1 _ => answer step_x1
    | ChooseRight _ _ step_x2 => answer step_x2
    | JoinLeft _ _ step_x1 _ => answer step_x1
    | JoinRight _ _ _ step_x2 => answer step_x2
    end.

  Fixpoint eval {E c A} (step : t c A) : C.t E A :=
    match step with
    | Call a => C.Ret _ a
    | Let _ _ step_x f => C.Let _ _ (eval step_x) f
    | LetDone _ _ _ _ _ _ step_f => eval step_f
    | ChooseLeft _ step_x1 x2 => C.Choose _ (eval step_x1) x2
    | ChooseRight _ x1 step_x2 => C.Choose _ x1 (eval step_x2)
    | JoinLeft _ _ step_x y => C.Join _ _ (eval step_x) y
    | JoinRight _ _ x step_y => C.Join _ _ x (eval step_y)
    end.
End Step.

Fixpoint compile {E A} (x : C.t E A) : Choose.t E A :=
  match x with
  | C.Ret _ v => Choose.Ret v
  | C.Call c => Choose.Call c Choose.Ret
  | C.Let _ _ x f => Choose.bind (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => Choose.Choose (compile x1) (compile x2)
  | C.Join _ _ x y => Choose.join (compile x) (compile y)
  end.*)
