Require Import Coq.Lists.List.
Require Import Io.All.

Import ListNotations.

(*Module Event.
  Record t (E : Effect.t) := New {
    c : Effect.command E;
    a : Effect.answer E c }.
  Arguments New {E} _ _.
  Arguments c {E} _.
  Arguments a {E} _.
End Event.*)

(*Module Model.
  Definition t (E : Effect.t) (S : Type) : Type :=
    forall c, S -> option (Effect.answer E c * S).
End Model.*)

(*Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> bool;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.*)

Module Trace.
  Inductive t (E : Effect.t) (T : Type) : Type :=
  | Ret : T -> t E T
  | Call : forall c, (Effect.answer E c -> t E T) -> t E T.
  Arguments Ret {E T} _.
  Arguments Call {E T} _ _.
End Trace.

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
    Inductive t {E : Effect.t} (c : Effect.command E) {A : Type}
      : Choose.t E A -> (Effect.answer E c -> Choose.t E A) -> Type :=
    | Call : forall h, t c (Choose.Call c h) h
    | ChooseLeft : forall (x1 x2 : Choose.t E A) k,
      t c x1 k ->
      t c (Choose.Choose x1 x2) k
    | ChooseRight : forall (x1 x2 : Choose.t E A) k,
      t c x2 k ->
      t c (Choose.Choose x1 x2) k.
  End Step.

  Module Steps.
    Inductive t {E : Effect.t} {A : Type} (x : Choose.t E A)
      : Trace.t E (Choose.t E A) -> Type :=
    | Nil : t x (Trace.Ret x)
    | Cons : forall c k trace,
      Step.t c x k -> (forall a, t (k a) (trace a)) ->
      t x (Trace.Call c trace).
  End Steps.

  Module LastSteps.
    Inductive t {E : Effect.t} {A : Type} (x : Choose.t E A)
      : Trace.t E A -> Type :=
    | Nil : forall v, LastStep.t x v -> t x (Trace.Ret v)
    | Cons : forall c k trace,
      Step.t c x k -> (forall a, t (k a) (trace a)) ->
      t x (Trace.Call c trace).
  End LastSteps.

  (*Module Steps.
    Inductive t {E : Effect.t} {A : Type}
      : list (Event.t E) -> Choose.t E A -> Choose.t E A -> Type :=
    | Nil : forall x, t [] x x
    | Cons : forall e es x x' x'',
      t es x x' -> Step.t e x' x'' ->
      t (e :: es) x x''.
  End Steps.

  Module LastSteps.
    Inductive t {E : Effect.t} {A : Type}
      (es : list (Event.t E)) (x : Choose.t E A) (v : A) : Type :=
    | New : forall x', Steps.t es x x' -> LastStep.t x' v -> t es x v.
  End LastSteps.*)

  Fixpoint map {E A B} (x : t E A) (f : A -> B) : t E B :=
    match x with
    | Ret v => Ret (f v)
    | Call c h => Call c (fun a => map (h a) f)
    | Choose x1 x2 => Choose (map x1 f) (map x2 f)
    end.

  Fixpoint bind {E} {A B} (x : t E A) (f : A -> t E B) : t E B :=
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

  Module Equiv.
    Fixpoint map {E} {A B} (x : t E A) (v : A) (f : A -> B)
      (H : LastStep.t x v) : LastStep.t (Choose.map x f) (f v).
      destruct H.
      - apply LastStep.Ret.
      - apply LastStep.ChooseLeft.
        now apply map.
      - apply LastStep.ChooseRight.
        now apply map.
    Defined.

    Fixpoint bind {E} c {A B} (x : t E A) (f : A -> t E B) k (H : Step.t c x k)
      : Step.t c (Choose.bind x f) (fun a => Choose.bind (k a) f).
      destruct H.
      - apply Step.Call.
      - apply Step.ChooseLeft.
        now apply bind.
      - apply Step.ChooseRight.
        now apply bind.
    Defined.

    Fixpoint bind_last {E} c {A B} (x : t E A) (v : A) (f : A -> t E B) k
      (H_x : LastStep.t x v) (H_f : Step.t c (f v) k)
      : Step.t c (Choose.bind x f) k.
      destruct H_x.
      - exact H_f.
      - apply Step.ChooseLeft.
        now apply bind_last with (v := v).
      - apply Step.ChooseRight.
        now apply bind_last with (v := v).
    Defined.

    Fixpoint bind_last_last {E} {A B} (x : t E A) (v_x : A) (f : A -> t E B)
      (v_y : B) (H_x : LastStep.t x v_x) (H_f : LastStep.t (f v_x) v_y)
      : LastStep.t (Choose.bind x f) v_y.
      destruct H_x.
      - exact H_f.
      - apply LastStep.ChooseLeft.
        now apply bind_last_last with (v_x := v).
      - apply LastStep.ChooseRight.
        now apply bind_last_last with (v_x := v).
    Defined.

    Fixpoint join_right {E} c {A B} (x : t E A) (y : t E B) k (H : Step.t c y k)
      : Step.t c (Choose.join_right x y) (fun a => Choose.join x (k a)).
      destruct H.
      - apply Step.Call.
      - apply Step.ChooseLeft.
        now apply join_right.
      - apply Step.ChooseRight.
        now apply join_right.
    Defined.

    Fixpoint join_left {E} c {A B} (x : t E A) (y : t E B) k (H : Step.t c x k)
      : Step.t c (Choose.join_left x y) (fun a => Choose.join (k a) y).
      destruct H.
      - apply Step.Call.
      - apply Step.ChooseLeft.
        now apply join_left.
      - apply Step.ChooseRight.
        now apply join_left.
    Defined.

    Fixpoint join_left_last {E} {A B} (x : t E A) (v_x : A) (y : t E B) (v_y : B)
      (H_x : LastStep.t x v_x) (H_y : LastStep.t y v_y)
      : LastStep.t (Choose.join_left x y) (v_x, v_y).
      destruct H_x.
      - now apply map.
      - apply LastStep.ChooseLeft.
        now apply join_left_last.
      - apply LastStep.ChooseRight.
        now apply join_left_last.
    Defined.
  End Equiv.
End Choose.

Module LastStep.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> A -> Type :=
  | Ret : forall A (v : A),
    t (C.Ret E v) v
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B) (v_x : A) (v_y : B),
    t x v_x -> t (f v_x) v_y ->
    t (C.Let _ _ x f) v_y
  | ChooseLeft : forall A (x1 x2 : C.t E A) (v : A),
    t x1 v ->
    t (C.Choose _ x1 x2) v
  | ChooseRight : forall A (x1 x2 : C.t E A) (v : A),
    t x2 v ->
    t (C.Choose _ x1 x2) v
  | Join : forall A B (x : C.t E A) (v_x : A) (y : C.t E B) (v_y : B),
    t x v_x -> t y v_y ->
    t (C.Join _ _ x y) (v_x, v_y).
End LastStep.

Module Step.
  Inductive t {E : Effect.t} (c : Effect.command E)
    : forall {A}, C.t E A -> (Effect.answer E c -> C.t E A) -> Type :=
  | Call : t c (C.Call c) (fun a => C.Ret _ a)
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B) k,
    t c x k ->
    t c (C.Let _ _ x f) (fun a => C.Let _ _ (k a) f)
  | LetDone : forall A B (x : C.t E A) (v : A) (f : A -> C.t E B) k,
    LastStep.t x v -> t c (f v) k ->
    t c (C.Let _ _ x f) k
  | ChooseLeft : forall A (x1 x2 : C.t E A) k,
    t c x1 k ->
    t c (C.Choose _ x1 x2) k
  | ChooseRight : forall A (x1 x2 : C.t E A) k,
    t c x2 k ->
    t c (C.Choose _ x1 x2) k
  | JoinLeft : forall A B (x : C.t E A) (y : C.t E B) k,
    t c x k ->
    t c (C.Join _ _ x y) (fun a => C.Join _ _ (k a) y)
  | JoinRight : forall A B (x : C.t E A) (y : C.t E B) k,
    t c y k ->
    t c (C.Join _ _ x y) (fun a => C.Join _ _ x (k a)).
End Step.

(*Module Steps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> C.t E A -> C.t E A -> Type :=
  | Nil : forall x, t [] x x
  | Cons : forall e es x x' x'',
    t es x x' -> Step.t e x' x'' ->
    t (e :: es) x x''.
End Steps.

Module LastSteps.
  Inductive t {E : Effect.t} {A : Type}
    (es : list (Event.t E)) (x : C.t E A) (v : A) : Type :=
  | New : forall x', Steps.t es x x' -> LastStep.t x' v -> t es x v.
End LastSteps.*)

Fixpoint compile {E} {A} (x : C.t E A) : Choose.t E A :=
  match x with
  | C.Ret _ v => Choose.Ret v
  | C.Call c => Choose.Call c Choose.Ret
  | C.Let _ _ x f => Choose.bind (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => Choose.Choose (compile x1) (compile x2)
  | C.Join _ _ x y => Choose.join (compile x) (compile y)
  end.

Module Equiv.
  Fixpoint last_step {E} {A} (x : C.t E A) (v : A) (H : LastStep.t x v)
    : Choose.LastStep.t (compile x) v.
    destruct H.
    - apply Choose.LastStep.Ret.
    - apply (Choose.Equiv.bind_last_last _ v_x).
      + now apply last_step.
      + now apply last_step.
    - apply Choose.LastStep.ChooseLeft.
      now apply last_step.
    - apply Choose.LastStep.ChooseRight.
      now apply last_step.
    - apply Choose.LastStep.ChooseLeft.
      apply Choose.Equiv.join_left_last.
      + now apply last_step.
      + now apply last_step.
  Defined.

  Fixpoint step {E} c {A} (x : C.t E A) k (H : Step.t c x k)
    : Choose.Step.t c (compile x) (fun a => compile (k a)).
    destruct H.
    - apply Choose.Step.Call.
    - apply Choose.Equiv.bind.
      now apply step.
    - apply (Choose.Equiv.bind_last c _ v).
      + now apply Equiv.last_step.
      + now apply step.
    - apply Choose.Step.ChooseLeft.
      now apply step.
    - apply Choose.Step.ChooseRight.
      now apply step.
    - apply Choose.Step.ChooseLeft.
      apply Choose.Equiv.join_left.
      now apply step.
    - apply Choose.Step.ChooseRight.
      apply Choose.Equiv.join_right.
      now apply step.
  Defined.
End Equiv.

(*Module DeadLockFree.
  Definition t {E : Effect.t} {A : Type} (x : C.t E A) : Type :=
    forall es x', Steps.t es x x' ->
      {es' : list (Event.t E) & {v : A & LastSteps.t es' x' v}}.
End DeadLockFree.*)
