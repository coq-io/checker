Require Import Coq.Lists.List.
Require Import Io.All.

Import ListNotations.

Module Event.
  Record t (E : Effect.t) := New {
    c : Effect.command E;
    a : Effect.answer E c }.
  Arguments New {E} _ _.
  Arguments c {E} _.
  Arguments a {E} _.
End Event.

(*Module Model.
  Definition t (E : Effect.t) (S : Type) : Type :=
    forall c, S -> option (Effect.answer E c * S).
End Model.*)

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> bool;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.

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

  Module ModelStep.
    Inductive t {E S} (m : Model.t E S) (s : S) (e : Event.t E) {A}
      : Choose.t E A -> Choose.t E A -> Type :=
    | New : Model.pre m 
  End ModelStep.

  Module Steps.
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
  End LastSteps.

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

    Fixpoint bind {E} (e : Event.t E) {A B} (x x' : t E A) (f : A -> t E B)
      (H : Step.t e x x') : Step.t e (Choose.bind x f) (Choose.bind x' f).
      destruct H.
      - apply (Step.Call e).
      - apply Step.ChooseLeft.
        now apply bind.
      - apply Step.ChooseRight.
        now apply bind.
    Defined.

    Fixpoint bind_last {E} (e : Event.t E) {A B} (x : t E A) (v : A)
      (f : A -> t E B) (y : t E B) (H_x : LastStep.t x v)
      (H_f : Step.t e (f v) y) : Step.t e (Choose.bind x f) y.
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

    Fixpoint join_right {E} (e : Event.t E) {A B} (x : t E A) (y y' : t E B)
      (H : Step.t e y y') : Step.t e (Choose.join_right x y) (Choose.join x y').
      destruct H.
      - apply (Step.Call e).
      - apply Step.ChooseLeft.
        now apply join_right.
      - apply Step.ChooseRight.
        now apply join_right.
    Defined.

    Fixpoint join_left {E} (e : Event.t E) {A B} (x x' : t E A) (y : t E B)
      (H : Step.t e x x') : Step.t e (Choose.join_left x y) (Choose.join x' y).
      destruct H.
      - apply (Step.Call e).
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
  Inductive t {E : Effect.t} (e : Event.t E)
    : forall {A}, C.t E A -> C.t E A -> Type :=
  | Call : t e (C.Call (Event.c e)) (C.Ret _ (Event.a e))
  | Let : forall A B (x x' : C.t E A) (f : A -> C.t E B),
    t e x x' ->
    t e (C.Let _ _ x f) (C.Let _ _ x' f)
  | LetDone : forall A B (x : C.t E A) (v : A) (f : A -> C.t E B) (y : C.t E B),
    LastStep.t x v -> t e (f v) y ->
    t e (C.Let _ _ x f) y
  | ChooseLeft : forall A (x1 x2 : C.t E A) x1',
    t e x1 x1' ->
    t e (C.Choose _ x1 x2) x1'
  | ChooseRight : forall A (x1 x2 : C.t E A) x2',
    t e x2 x2' ->
    t e (C.Choose _ x1 x2) x2'
  | JoinLeft : forall A B (x x' : C.t E A) (y : C.t E B),
    t e x x' ->
    t e (C.Join _ _ x y) (C.Join _ _ x' y)
  | JoinRight : forall A B (x : C.t E A) (y y' : C.t E B),
    t e y y' ->
    t e (C.Join _ _ x y) (C.Join _ _ x y').
End Step.

Module Steps.
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
End LastSteps.

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

  Fixpoint step {E} (e : Event.t E) {A} (x x' : C.t E A) (H : Step.t e x x')
    : Choose.Step.t e (compile x) (compile x').
    destruct H.
    - apply Choose.Step.Call.
    - apply Choose.Equiv.bind.
      now apply step.
    - apply (Choose.Equiv.bind_last e _ v).
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

Module DeadLockFree.
  Definition t {E : Effect.t} {A : Type} (x : C.t E A) : Type :=
    forall es x', Steps.t es x x' ->
      {es' : list (Event.t E) & {v : A & LastSteps.t es' x' v}}.
End DeadLockFree.
