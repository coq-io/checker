Require Import Coq.Lists.List.
Require Import Io.All.
Require Event.

Import ListNotations.

Inductive t (E : Effect.t) (A : Type) : Type :=
| Ret : A -> t E A
| Call : forall c, (Effect.answer E c -> t E A) -> t E A
| Choose : t E A -> t E A -> t E A.
Arguments Ret {E A} _.
Arguments Call {E A} _ _.
Arguments Choose {E A} _ _.

Module LastStep.
  Inductive t {E : Effect.t} {A : Type} : Choose.t E A -> A -> Prop :=
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
    : Choose.t E A -> Choose.t E A -> Prop :=
  | Call : forall h, t e (Choose.Call (Event.c e) h) (h (Event.a e))
  | ChooseLeft : forall (x1 x2 : Choose.t E A) k,
    t e x1 k ->
    t e (Choose.Choose x1 x2) k
  | ChooseRight : forall (x1 x2 : Choose.t E A) k,
    t e x2 k ->
    t e (Choose.Choose x1 x2) k.
End Step.

Module Steps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> Choose.t E A -> Choose.t E A -> Prop :=
  | Nil : forall x, t [] x x
  | Cons : forall e x x' es x'',
    Step.t e x x' -> t es x' x'' ->
    t (e :: es) x x''.
End Steps.

Module LastSteps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> Choose.t E A -> A -> Prop :=
  | Nil : forall x v, LastStep.t x v -> t [] x v
  | Cons : forall e x x' es v,
    Step.t e x x' -> t es x' v ->
    t (e :: es) x v.
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

Module Complete.
  Module Last.
    Fixpoint map {E} {A B} (x : t E A) (v : A) (f : A -> B)
      (H : LastStep.t x v) : LastStep.t (Choose.map x f) (f v).
      destruct H.
      - apply LastStep.Ret.
      - apply LastStep.ChooseLeft.
        now apply map.
      - apply LastStep.ChooseRight.
        now apply map.
    Qed.

    Fixpoint bind_left {E} e {A B} (x : t E A) (v : A) (f : A -> t E B)
      (y : t E B) (H_x : LastStep.t x v) (H_f : Step.t e (f v) y)
      : Step.t e (Choose.bind x f) y.
      destruct H_x.
      - exact H_f.
      - apply Step.ChooseLeft.
        now apply bind_left with (v := v).
      - apply Step.ChooseRight.
        now apply bind_left with (v := v).
    Qed.

    Fixpoint bind_both {E} {A B} (x : t E A) (v_x : A) (f : A -> t E B)
      (v_y : B) (H_x : LastStep.t x v_x) (H_f : LastStep.t (f v_x) v_y)
      : LastStep.t (Choose.bind x f) v_y.
      destruct H_x.
      - exact H_f.
      - apply LastStep.ChooseLeft.
        now apply bind_both with (v_x := v).
      - apply LastStep.ChooseRight.
        now apply bind_both with (v_x := v).
    Qed.

    Fixpoint join_left {E A B} (x : t E A) (v_x : A) (y : t E B) (v_y : B)
      (H_x : LastStep.t x v_x) (H_y : LastStep.t y v_y)
      : LastStep.t (Choose.join_left x y) (v_x, v_y).
      destruct H_x.
      - now apply map.
      - apply LastStep.ChooseLeft.
        now apply join_left.
      - apply LastStep.ChooseRight.
        now apply join_left.
    Qed.
  End Last.

  Fixpoint bind {E} e {A B} (x x' : t E A) (f : A -> t E B) (H : Step.t e x x')
    : Step.t e (Choose.bind x f) (Choose.bind x' f).
    destruct H.
    - apply (Step.Call e).
    - apply Step.ChooseLeft.
      now apply bind.
    - apply Step.ChooseRight.
      now apply bind.
  Qed.

  Fixpoint join_right {E} e {A B} (x : t E A) (y y' : t E B) (H : Step.t e y y')
    : Step.t e (Choose.join_right x y) (Choose.join x y').
    destruct H.
    - apply (Step.Call e).
    - apply Step.ChooseLeft.
      now apply join_right.
    - apply Step.ChooseRight.
      now apply join_right.
  Qed.

  Fixpoint join_left {E} e {A B} (x x' : t E A) (y : t E B) (H : Step.t e x x')
    : Step.t e (Choose.join_left x y) (Choose.join x' y).
    destruct H.
    - apply (Step.Call e).
    - apply Step.ChooseLeft.
      now apply join_left.
    - apply Step.ChooseRight.
      now apply join_left.
  Qed.
End Complete.

Module Sound.
  Module Last.
    Fixpoint choose {E A} {x1 x2 : t E A} {v : A}
      (H : LastStep.t (Choose x1 x2) v) : LastStep.t x1 v \/ LastStep.t x2 v.
      inversion H.
      - now left.
      - now right.
    Qed.

    Fixpoint map {E A B} {x : t E A} {f : A -> B} {v : B}
      (H : LastStep.t (Choose.map x f) v)
      : exists v_x, LastStep.t x v_x /\ f v_x = v.
      destruct x as [v_x | c h | x1 x2].
      - exists v_x.
        split.
        + apply LastStep.Ret.
        + now inversion H.
      - inversion H.
      - destruct (choose H) as [H1 | H2].
        + destruct (map _ _ _ _ _ _ H1) as [v_x1 H_x1].
          exists v_x1.
          split.
          * now apply LastStep.ChooseLeft.
          * now destruct H_x1.
        + destruct (map _ _ _ _ _ _ H2) as [v_x2 H_x2].
          exists v_x2.
          split.
          * now apply LastStep.ChooseRight.
          * now destruct H_x2.
    Qed.

    Fixpoint bind {E A B} (x : t E A) (f : A -> t E B) (v : B)
      (H : LastStep.t (Choose.bind x f) v)
      : exists v_x, LastStep.t x v_x /\ LastStep.t (f v_x) v.
      destruct x as [v_x | c h | x1 x2].
      - exists v_x.
        split.
        + apply LastStep.Ret.
        + apply H.
      - inversion H.
      - destruct (choose H) as [H1 | H2].
        + destruct (bind _ _ _ _ _ _ H1) as [v_x1 H_x1].
          exists v_x1.
          split.
          * now apply LastStep.ChooseLeft.
          * now destruct H_x1.
        + destruct (bind _ _ _ _ _ _ H2) as [v_x2 H_x2].
          exists v_x2.
          split.
          * now apply LastStep.ChooseRight.
          * now destruct H_x2.
    Qed.

    Fixpoint join_right {E A B} (x : t E A) (y : t E B) v_x v_y
      (H : LastStep.t (Choose.join_right x y) (v_x, v_y))
      : LastStep.t x v_x /\ LastStep.t y v_y.
      destruct y as [v'_y | c h | y1 y2].
      - simpl in H.
        destruct (map H) as [v'_x H_x].
        destruct H_x.
        assert (H_eq_x : v_x = v'_x) by congruence.
        assert (H_eq_y : v_y = v'_y) by congruence.
        split.
        + now rewrite H_eq_x.
        + rewrite H_eq_y.
          apply LastStep.Ret.
      - inversion H.
      - simpl in H.
        destruct (choose H) as [H1 | H2].
        + destruct (join_right _ _ _ _ _ _ _ H1).
          split.
          * trivial.
          * now apply LastStep.ChooseLeft.
        + destruct (join_right _ _ _ _ _ _ _ H2).
          split.
          * trivial.
          * now apply LastStep.ChooseRight.
    Qed.

    Fixpoint join_left {E A B} (x : t E A) (y : t E B) v_x v_y
      (H : LastStep.t (Choose.join_left x y) (v_x, v_y))
      : LastStep.t x v_x /\ LastStep.t y v_y.
      destruct x as [v'_x | c h | x1 x2].
      - simpl in H.
        destruct (map H) as [v'_y H_y].
        destruct H_y.
        assert (H_eq_x : v_x = v'_x) by congruence.
        assert (H_eq_y : v_y = v'_y) by congruence.
        split.
        + rewrite H_eq_x.
          apply LastStep.Ret.
        + now rewrite H_eq_y.
      - inversion H.
      - simpl in H.
        destruct (choose H) as [H1 | H2].
        + destruct (join_left _ _ _ _ _ _ _ H1).
          split.
          * now apply LastStep.ChooseLeft.
          * trivial.
        + destruct (join_left _ _ _ _ _ _ _ H2).
          split.
          * now apply LastStep.ChooseRight.
          * trivial.
    Qed.

    Definition join {E A B} {x : t E A} {y : t E B} {v_x v_y}
      (H : LastStep.t (Choose.join x y) (v_x, v_y))
      : LastStep.t x v_x /\ LastStep.t y v_y.
      destruct (choose H).
      - now apply join_left.
      - now apply join_right.
    Qed.
  End Last.
End Sound.

(*Fixpoint check {E S} (m : Model.t E S) (s : S) (dec : Model.Dec.t m) {A}
  (x : t E A) : bool.
  destruct x as [v | c h | x1 x2].
  - exact true.
  - 
Defined.*)