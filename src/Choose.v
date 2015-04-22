Require Import Coq.Lists.List.
Require Import Io.All.

Import ListNotations.
Local Open Scope type.

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
  Inductive t {E : Effect.t} {A : Type} : Choose.t E A -> Type :=
  | Call : forall c h (a : Effect.answer E c), t (Choose.Call c h)
  | ChooseLeft : forall (x1 x2 : Choose.t E A),
    t x1 ->
    t (Choose.Choose x1 x2)
  | ChooseRight : forall (x1 x2 : Choose.t E A),
    t x2 ->
    t (Choose.Choose x1 x2).

  Fixpoint eval {E A} {x : Choose.t E A} (H : t x) : Choose.t E A :=
    match H with
    | Call _ h a => h a
    | ChooseLeft _ _ H_x1 => eval H_x1
    | ChooseRight _ _ H_x2 => eval H_x2
    end.
End Step.

(*Module LastSteps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> Choose.t E A -> A -> Prop :=
  | Nil : forall x v, LastStep.t x v -> t [] x v
  | Cons : forall e x x' es v,
    Step.t e x x' -> t es x' v ->
    t (e :: es) x v.
End LastSteps.

Module Steps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> Choose.t E A -> Choose.t E A -> Prop :=
  | Nil : forall x, t [] x x
  | Cons : forall e x x' es x'',
    Step.t e x x' -> t es x' x'' ->
    t (e :: es) x x''.
End Steps.*)

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

Module Complete.
  Module Last.
    Fixpoint map {E A B} (x : t E A) (v : A) (f : A -> B)
      (H : LastStep.t x v) : LastStep.t (Choose.map x f) (f v).
      destruct H.
      - apply LastStep.Ret.
      - apply LastStep.ChooseLeft.
        now apply map.
      - apply LastStep.ChooseRight.
        now apply map.
    Defined.

    Fixpoint bind {E A B} (x : t E A) (v_x : A) (f : A -> t E B)
      (v_y : B) (H_x : LastStep.t x v_x) (H_f : LastStep.t (f v_x) v_y)
      : LastStep.t (Choose.bind x f) v_y.
      destruct H_x.
      - exact H_f.
      - apply LastStep.ChooseLeft.
        now apply bind with (v_x := v).
      - apply LastStep.ChooseRight.
        now apply bind with (v_x := v).
    Defined.

    Fixpoint join_left {E A B} (x : t E A) (v_x : A) (y : t E B) (v_y : B)
      (H_x : LastStep.t x v_x) (H_y : LastStep.t y v_y)
      : LastStep.t (Choose.join_left x y) (v_x, v_y).
      destruct H_x.
      - now apply map.
      - apply LastStep.ChooseLeft.
        now apply join_left.
      - apply LastStep.ChooseRight.
        now apply join_left.
    Defined.
  End Last.

  Fixpoint bind_left {E A B} (x : t E A) (v : A) (f : A -> t E B)
    (H_x : LastStep.t x v) (H_f : Step.t (f v)) : Step.t (Choose.bind x f).
    destruct H_x.
    - exact H_f.
    - apply Step.ChooseLeft.
      now apply bind_left with (v := v).
    - apply Step.ChooseRight.
      now apply bind_left with (v := v).
  Defined.

  Fixpoint bind_right {E A B} (x : t E A) (f : A -> t E B) (H : Step.t x)
    : Step.t (Choose.bind x f) (*Choose.bind x' f*).
    destruct H.
    - exact (Step.Call c _ a).
    - apply Step.ChooseLeft.
      now apply bind_right.
    - apply Step.ChooseRight.
      now apply bind_right.
  Defined.

  Fixpoint join_right {E A B} (x : t E A) (y : t E B) (H : Step.t y)
    : Step.t (Choose.join_right x y) (*Choose.join x y'*).
    destruct H.
    - exact (Step.Call c _ a).
    - apply Step.ChooseLeft.
      now apply join_right.
    - apply Step.ChooseRight.
      now apply join_right.
  Defined.

  Fixpoint join_left {E A B} (x : t E A) (y : t E B) (H : Step.t x)
    : Step.t (Choose.join_left x y) (*Choose.join x' y*).
    destruct H.
    - exact (Step.Call c _ a).
    - apply Step.ChooseLeft.
      now apply join_left.
    - apply Step.ChooseRight.
      now apply join_left.
  Defined.
End Complete.

Module Sound.
  Module Last.
    Fixpoint choose {E A} {x1 x2 : t E A} {v : A}
      (H : LastStep.t (Choose x1 x2) v) : LastStep.t x1 v + LastStep.t x2 v.
      inversion H.
      - now left.
      - now right.
    Defined.

    Fixpoint map {E A B} {x : t E A} {f : A -> B} {v : B}
      (H : LastStep.t (Choose.map x f) v)
      : {v_x : A & LastStep.t x v_x * (f v_x = v)}.
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
          * apply LastStep.ChooseLeft.
            now destruct H_x1.
          * now destruct H_x1.
        + destruct (map _ _ _ _ _ _ H2) as [v_x2 H_x2].
          exists v_x2.
          split.
          * apply LastStep.ChooseRight.
            now destruct H_x2.
          * now destruct H_x2.
    Defined.

    Fixpoint bind {E A B} (x : t E A) (f : A -> t E B) (v : B)
      (H : LastStep.t (Choose.bind x f) v)
      : {v_x : A & LastStep.t x v_x * LastStep.t (f v_x) v}.
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
          * apply LastStep.ChooseLeft.
            now destruct H_x1.
          * now destruct H_x1.
        + destruct (bind _ _ _ _ _ _ H2) as [v_x2 H_x2].
          exists v_x2.
          split.
          * apply LastStep.ChooseRight.
            now destruct H_x2.
          * now destruct H_x2.
    Defined.

    Fixpoint join_right {E A B} (x : t E A) (y : t E B) v_x v_y
      (H : LastStep.t (Choose.join_right x y) (v_x, v_y))
      : LastStep.t x v_x * LastStep.t y v_y.
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
    Defined.

    Fixpoint join_left {E A B} (x : t E A) (y : t E B) v_x v_y
      (H : LastStep.t (Choose.join_left x y) (v_x, v_y))
      : LastStep.t x v_x * LastStep.t y v_y.
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
    Defined.

    Definition join {E A B} {x : t E A} {y : t E B} {v_x v_y}
      (H : LastStep.t (Choose.join x y) (v_x, v_y))
      : LastStep.t x v_x * LastStep.t y v_y.
      destruct (choose H).
      - now apply join_left.
      - now apply join_right.
    Defined.
  End Last.

  Fixpoint map {E A B} {x : t E A} {f : A -> B} (H : Step.t (map x f))
    : Step.t x.
    destruct x; simpl in H.
    - inversion H.
    - apply Step.Call.
      exact (
        match H in Step.t x return
          match x with
          | Call c _ => answer E c
          | _ => unit
          end with
        | Step.Call _ _ a => a
        | _ => tt
        end).
    - inversion_clear H as [| x1_ x2_ H_x1 | x1_ x2_ H_x2].
      + apply Step.ChooseLeft.
        apply (map _ _ _ _ _ H_x1).
      + apply Step.ChooseRight.
        apply (map _ _ _ _ _ H_x2).
  Defined.

  Fixpoint bind {E A B} {x : t E A} {f : A -> t E B}
    (H : Step.t (Choose.bind x f))
    : {v : A & LastStep.t x v * Step.t (f v)} + Step.t x.
    destruct x; simpl in H.
    - left.
      exists a.
      split.
      + apply LastStep.Ret.
      + apply H.
    - right.
      apply Step.Call.
      exact (
        match H in Step.t x return
          match x with
          | Call c _ => answer E c
          | _ => unit
          end with
        | Step.Call _ _ a => a
        | _ => tt
        end).
    - inversion_clear H as [| x1_ x2_ H_left | x1_ x2_ H_right].
      + destruct (bind _ _ _ _ _ H_left) as [[v [H_v H_f]]| H_x1].
        * left.
          exists v.
          split; [now apply LastStep.ChooseLeft | apply H_f].
        * right.
          now apply Step.ChooseLeft.
      + destruct (bind _ _ _ _ _ H_right) as [[v [H_v H_f]]| H_x2].
        * left.
          exists v.
          split; [now apply LastStep.ChooseRight | apply H_f].
        * right.
          now apply Step.ChooseRight.
  Defined.

  Fixpoint join_left {E A B} {x : t E A} {y : t E B}
    (H : Step.t (Choose.join_left x y)) : Step.t x + Step.t y.
    destruct x as [v | c h | x1 x2];
      unfold Choose.join_left in H; simpl in H.
    - right.
      apply (map H).
    - left.
      apply Step.Call.
      exact (
        match H in Step.t x return
          match x with
          | Call c _ => answer E c
          | _ => unit
          end with
        | Step.Call _ _ a => a
        | _ => tt
        end).
    - inversion_clear H as [| x1_ x2_ H_x1 | x1_ x2_ H_x2].
      + destruct (join_left _ _ _ _ _ H_x1) as [H_x | H_y].
        * left.
          now apply Step.ChooseLeft.
        * now right.
      + destruct (join_left _ _ _ _ _ H_x2) as [H_x | H_y].
        * left.
          now apply Step.ChooseRight.
        * now right.
  Defined.

  Fixpoint join_right {E A B} {x : t E A} {y : t E B}
    (H : Step.t (Choose.join_right x y)) : Step.t x + Step.t y.
    destruct y as [v | c h | y1 y2]; simpl in H.
    - left.
      apply (map H).
    - right.
      apply Step.Call.
      exact (
        match H in Step.t x return
          match x with
          | Call c _ => answer E c
          | _ => unit
          end with
        | Step.Call _ _ a => a
        | _ => tt
        end).
    - inversion_clear H as [| x1_ x2_ H_x1 | x1_ x2_ H_x2].
      + destruct (join_right _ _ _ _ _ H_x1) as [H_x | H_y].
        * now left.
        * right.
          now apply Step.ChooseLeft.
      + destruct (join_right _ _ _ _ _ H_x2) as [H_x | H_y].
        * now left.
        * right.
          now apply Step.ChooseRight.
  Defined.
End Sound.

(*Fixpoint check {E S} (m : Model.t E S) (s : S) (dec : Model.Dec.t m) {A}
  (x : t E A) : bool.
  destruct x as [v | c h | x1 x2].
  - exact true.
  - 
Defined.*)
