Require Import Coq.Lists.List.

Import ListNotations.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Event.
  Record t (E : Effect.t) := New {
    c : Effect.command E;
    a : Effect.answer E c }.
  Arguments New {E} _ _.
  Arguments c {E} _.
  Arguments a {E} _.
End Event.

Module Choose.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Choose : t E A -> t E A -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Choose {E A} _ _.

  Module LastStep.
    Inductive t {E : Effect.t} {A : Type} : Choose.t E A -> A -> Type :=
    | Ret : forall v,
      t (Choose.Ret v) v
    | ChooseLeft : forall (x1 x2 : Choose.t E A) (v : A),
      t x1 v ->
      t (Choose.Choose x1 x2) v
    | ChooseRight : forall (x1 x2 : Choose.t E A) (v : A),
      t x2 v ->
      t (Choose.Choose x1 x2) v.
  End LastStep.

  Module Step.
    Inductive t {E : Effect.t} (e : Event.t E) {A : Type}
      : Choose.t E A -> Choose.t E A -> Type :=
    | Call : forall h,
      t e (Choose.Call (Event.c e) h) (h (Event.a e))
    | ChooseLeft : forall (x1 x2 : Choose.t E A) x1',
      t e x1 x1' ->
      t e (Choose.Choose x1 x2) x1'
    | ChooseRight : forall (x1 x2 : Choose.t E A) x2',
      t e x2 x2' ->
      t e (Choose.Choose x1 x2) x2'.
  End Step.

  Fixpoint map {E A B} (x : t E A) (f : A -> B) : t E B :=
    match x with
    | Ret v => Ret (f v)
    | Call c h => Call c (fun a => map (h a) f)
    | Choose x1 x2 => Choose (map x1 f) (map x2 f)
    end.

  Fixpoint equiv_map {E} {A B} (x : t E A) (v : A) (f : A -> B)
    (H : LastStep.t x v) : LastStep.t (map x f) (f v).
    destruct H.
    - apply LastStep.Ret.
    - apply LastStep.ChooseLeft.
      now apply equiv_map.
    - apply LastStep.ChooseRight.
      now apply equiv_map.
  Defined.

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

  Fixpoint equiv_right {E} (e : Event.t E) {A B} (x : t E A) (y y' : t E B)
    (H : Step.t e y y') {struct H} : Step.t e (join_right x y) (join x y').
    destruct H.
    - apply (Step.Call e).
    - apply Step.ChooseLeft.
      now apply equiv_right.
    - apply Step.ChooseRight.
      now apply equiv_right.
  Defined.

  Fixpoint equiv_left {E} (e : Event.t E) {A B} (x x' : t E A) (y : t E B)
    (H : Step.t e x x') {struct H} : Step.t e (join_left x y) (join x' y).
    destruct H as [h | x1 x2 x1' Hx1x1' | x1 x2 x2' Hx2x2'].
    - apply (Step.Call e).
    - apply Step.ChooseLeft.
      now apply equiv_left.
    - apply Step.ChooseRight.
      now apply equiv_left.
  Defined.

  Fixpoint equiv_join_left_last {E} {A B} (x : t E A) (v_x : A) (y : t E B) (v_y : B)
    (H_x : LastStep.t x v_x) (H_y : LastStep.t y v_y)
    : LastStep.t (join_left x y) (v_x, v_y).
    destruct H_x.
    - now apply equiv_map.
    - apply LastStep.ChooseLeft.
      now apply equiv_join_left_last.
    - apply LastStep.ChooseRight.
      now apply equiv_join_left_last.
  Defined.

  Fixpoint bind {E} {A B} (x : t E A) (f : A -> t E B) : t E B :=
    match x with
    | Ret v => f v
    | Call c h => Call c (fun a => bind (h a) f)
    | Choose x1 x2 => Choose (bind x1 f) (bind x2 f)
    end.

  Fixpoint equiv_bind {E} (e : Event.t E) {A B} (x x' : t E A) (f : A -> t E B)
    (H : Step.t e x x') : Step.t e (bind x f) (bind x' f).
    destruct H.
    - apply (Step.Call e).
    - apply Step.ChooseLeft.
      now apply equiv_bind.
    - apply Step.ChooseRight.
      now apply equiv_bind.
  Defined.

  Fixpoint equiv_bind_last {E} (e : Event.t E) {A B} (x : t E A) (v : A)
    (f : A -> t E B) (y : t E B) (H_x : LastStep.t x v) (H_f : Step.t e (f v) y)
    : Step.t e (bind x f) y.
    destruct H_x.
    - exact H_f.
    - apply Step.ChooseLeft.
      now apply equiv_bind_last with (v := v).
    - apply Step.ChooseRight.
      now apply equiv_bind_last with (v := v).
  Defined.

  Fixpoint equiv_bind_last_last {E} {A B} (x : t E A) (v_x : A) (f : A -> t E B)
    (v_y : B) (H_x : LastStep.t x v_x) (H_f : LastStep.t (f v_x) v_y)
    : LastStep.t (bind x f) v_y.
    destruct H_x.
    - exact H_f.
    - apply LastStep.ChooseLeft.
      now apply equiv_bind_last_last with (v_x := v).
    - apply LastStep.ChooseRight.
      now apply equiv_bind_last_last with (v_x := v).
  Defined.
End Choose.

Module Join.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall A, A -> t E A
  | Call : forall A c, (Effect.answer E c -> t E A) -> t E A
  | Let : forall A B, t E A -> (A -> t E B) -> t E B
  | Choose : forall A, t E A -> t E A -> t E A
  | Join : forall A B, t E A -> t E B -> t E (A * B).
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Let {E A B} _ _.
  Arguments Choose {E A} _ _.
  Arguments Join {E A B} _ _.

  Module LastStep.
    Inductive t {E : Effect.t} : forall {A}, Join.t E A -> A -> Type :=
    | Ret : forall A (v : A),
      t (Join.Ret v) v
    | Let : forall A B (x : Join.t E A) (f : A -> Join.t E B) (v_x : A) (v_y : B),
      t x v_x -> t (f v_x) v_y ->
      t (Join.Let x f) v_y
    | ChooseLeft : forall A (x1 x2 : Join.t E A) (v : A),
      t x1 v ->
      t (Join.Choose x1 x2) v
    | ChooseRight : forall A (x1 x2 : Join.t E A) (v : A),
      t x2 v ->
      t (Join.Choose x1 x2) v
    | Join : forall A B (x : Join.t E A) (v_x : A) (y : Join.t E B) (v_y : B),
      t x v_x -> t y v_y ->
      t (Join.Join x y) (v_x, v_y).
  End LastStep.

  Module Step.
    Inductive t {E : Effect.t} (e : Event.t E)
      : forall {A}, Join.t E A -> Join.t E A -> Type :=
    | Call : forall A h,
      t (A := A) e (Join.Call (Event.c e) h) (h (Event.a e))
    | Let : forall A B (x x' : Join.t E A) (f : A -> Join.t E B),
      t e x x' ->
      t e (Join.Let x f) (Join.Let x' f)
    | LetDone : forall A B (x : Join.t E A) (v : A) (f : A -> Join.t E B) (y : Join.t E B),
      LastStep.t x v -> t e (f v) y ->
      t e (Join.Let x f) y
    | ChooseLeft : forall A (x1 x2 : Join.t E A) x1',
      t e x1 x1' ->
      t e (Join.Choose x1 x2) x1'
    | ChooseRight : forall A (x1 x2 : Join.t E A) x2',
      t e x2 x2' ->
      t e (Join.Choose x1 x2) x2'
    | JoinLeft : forall A B (x x' : Join.t E A) (y : Join.t E B),
      t e x x' ->
      t e (Join.Join x y) (Join.Join x' y)
    | JoinRight : forall A B (x : Join.t E A) (y y' : Join.t E B),
      t e y y' ->
      t e (Join.Join x y) (Join.Join x y').
  End Step.

  Fixpoint compile {E} {A} (x : t E A) : Choose.t E A :=
    match x with
    | Ret _ v => Choose.Ret v
    | Call _ c h => Choose.Call c (fun a => compile (h a))
    | Let _ _ x f => Choose.bind (compile x) (fun x => compile (f x))
    | Choose _ x1 x2 => Choose.Choose (compile x1) (compile x2)
    | Join _ _ x y => Choose.join (compile x) (compile y)
    end.

  Fixpoint equiv_last_step {E} {A} (x : t E A) (v : A) (H : LastStep.t x v)
    : Choose.LastStep.t (compile x) v.
    destruct H.
    - apply Choose.LastStep.Ret.
    - apply (Choose.equiv_bind_last_last _ v_x).
      + now apply equiv_last_step.
      + now apply equiv_last_step.
    - apply Choose.LastStep.ChooseLeft.
      now apply equiv_last_step.
    - apply Choose.LastStep.ChooseRight.
      now apply equiv_last_step.
    - apply Choose.LastStep.ChooseLeft.
      apply Choose.equiv_join_left_last.
      + now apply equiv_last_step.
      + now apply equiv_last_step.
  Defined.

  Fixpoint equiv_step {E} (e : Event.t E) {A} (x x' : t E A) (H : Step.t e x x')
    {struct H} : Choose.Step.t e (compile x) (compile x').
    destruct H.
    - apply (Choose.Step.Call e).
    - apply Choose.equiv_bind.
      now apply equiv_step.
    - apply (Choose.equiv_bind_last e _ v).
      + now apply equiv_last_step.
      + now apply equiv_step.
    - apply Choose.Step.ChooseLeft.
      now apply equiv_step.
    - apply Choose.Step.ChooseRight.
      now apply equiv_step.
    - apply Choose.Step.ChooseLeft.
      apply Choose.equiv_left.
      now apply equiv_step.
    - apply Choose.Step.ChooseRight.
      apply Choose.equiv_right.
      now apply equiv_step.
  Defined.
End Join.
