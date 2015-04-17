Require Import Coq.Lists.List.
Require Import Io.All.
Require Choose.

Import ListNotations.

Module LastStep.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> A -> Prop :=
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
  Inductive t {E : Effect.t}
    : forall {A}, Event.t E -> C.t E A -> C.t E A -> Prop :=
  | Call : forall c a, t (Event.New c a) (C.Call c) (C.Ret _ a)
  | Let : forall e A B (x x' : C.t E A) (f : A -> C.t E B),
    t e x x' ->
    t e (C.Let _ _ x f) (C.Let _ _ x' f)
  | LetDone : forall e A B (x : C.t E A) (v : A) (f : A -> C.t E B) (y : C.t E B),
    LastStep.t x v -> t e (f v) y ->
    t e (C.Let _ _ x f) y
  | ChooseLeft : forall e A (x1 x2 x1' : C.t E A),
    t e x1 x1' ->
    t e (C.Choose _ x1 x2) x1'
  | ChooseRight : forall e A (x1 x2 x2' : C.t E A),
    t e x2 x2' ->
    t e (C.Choose _ x1 x2) x2'
  | JoinLeft : forall e A B (x x' : C.t E A) (y : C.t E B),
    t e x x' ->
    t e (C.Join _ _ x y) (C.Join _ _ x' y)
  | JoinRight : forall e A B (x : C.t E A) (y y' : C.t E B),
    t e y y' ->
    t e (C.Join _ _ x y) (C.Join _ _ x y').
End Step.

Module LastSteps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> C.t E A -> A -> Prop :=
  | Nil : forall x v, LastStep.t x v -> t [] x v
  | Cons : forall e x x' es v,
    Step.t e x x' -> t es x' v ->
    t (e :: es) x v.
End LastSteps.

Module Steps.
  Inductive t {E : Effect.t} {A : Type}
    : list (Event.t E) -> C.t E A -> C.t E A -> Prop :=
  | Nil : forall x, t [] x x
  | Cons : forall e x x' es x'',
    Step.t e x x' -> t es x' x'' ->
    t (e :: es) x x''.
End Steps.

Fixpoint compile {E A} (x : C.t E A) : Choose.t E A :=
  match x with
  | C.Ret _ v => Choose.Ret v
  | C.Call c => Choose.Call c Choose.Ret
  | C.Let _ _ x f => Choose.bind (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => Choose.Choose (compile x1) (compile x2)
  | C.Join _ _ x y => Choose.join (compile x) (compile y)
  end.

Module Complete.
  Module Last.
    Fixpoint step {E A} (x : C.t E A) (v : A) (H : LastStep.t x v)
      : Choose.LastStep.t (compile x) v.
      destruct H.
      - apply Choose.LastStep.Ret.
      - apply (Choose.Complete.Last.bind_both _ v_x).
        + now apply step.
        + now apply step.
      - apply Choose.LastStep.ChooseLeft.
        now apply step.
      - apply Choose.LastStep.ChooseRight.
        now apply step.
      - apply Choose.LastStep.ChooseLeft.
        apply Choose.Complete.Last.join_left.
        + now apply step.
        + now apply step.
    Qed.
  End Last.

  Fixpoint step {E} e {A} (x x' : C.t E A) (H : Step.t e x x')
    : Choose.Step.t e (compile x) (compile x').
    destruct H.
    - apply Choose.Step.Call.
    - apply Choose.Complete.bind.
      now apply step.
    - apply (Choose.Complete.Last.bind_left _ _ v).
      + now apply Last.step.
      + now apply step.
    - apply Choose.Step.ChooseLeft.
      now apply step.
    - apply Choose.Step.ChooseRight.
      now apply step.
    - apply Choose.Step.ChooseLeft.
      apply Choose.Complete.join_left.
      now apply step.
    - apply Choose.Step.ChooseRight.
      apply Choose.Complete.join_right.
      now apply step.
  Qed.

  (*Fixpoint traces {E A} (x : C.t E A) trace (H : Steps.t x trace)
    : Choose.Steps.t (compile x) (Trace.map compile trace).
    destruct H.
    - apply Choose.Steps.Nil.
    - apply (Choose.Steps.Cons _ _ (fun a => compile (k a))).
      + now apply step.
      + intro.
        now apply traces.
  Qed.

  Fixpoint last_traces {E A} (x : C.t E A) (trace : Trace.t E A)
    (H : LastSteps.t x trace) : Choose.LastSteps.t (compile x) trace.
    destruct H.
    - apply Choose.LastSteps.Nil.
      now apply last_step.
    - apply (Choose.LastSteps.Cons _ _ (fun a => compile (k a))).
      + now apply step.
      + intro.
        now apply last_traces.
  Qed.*)
End Complete.

Module Sound.
  Module Last.
    Fixpoint step {E A} (x : C.t E A) (v : A)
      (H : Choose.LastStep.t (compile x) v) : LastStep.t x v.
      destruct x; simpl in H.
      - inversion_clear H.
        apply LastStep.Ret.
      - inversion_clear H.
      - destruct (Choose.Sound.Last.bind _ _ _ H) as [v_x H_x].
        apply (LastStep.Let _ _ _ _ v_x).
        + now apply step.
        + now apply step.
      - destruct (Choose.Sound.Last.choose H).
        + apply LastStep.ChooseLeft.
          now apply step.
        + apply LastStep.ChooseRight.
          now apply step.
      - destruct v as [v_x v_y].
        destruct (Choose.Sound.Last.join H).
        apply LastStep.Join.
        + now apply step.
        + now apply step.
    Qed.
  End Last.

  Fixpoint step {E A} (x x' : C.t E A) e
    (H : Choose.Step.t e (compile x) (compile x')) : Step.t e x x'.
    (*case_eq x.*)
    (* destruct e. *)
    destruct x as [v | c | x f | x1 x2 | x y]; simpl in H.
    - inversion H.
    - inversion H.
      assert (e' : Event.t E) by admit.
      assert (e = e') by admit.
      rewrite H0.
      rewrite <- H1.
 assert (exists a, x' = C.Ret _ a).
      admit.
      destruct H0.
      rewrite H0.
      apply Step.Call.
  Qed.

  (*Fixpoint last_traces {E A} (x : C.t E A) (trace : Trace.t E A)
    (H : Choose.LastSteps.t (compile x) trace) : LastSteps.t x trace.
    destruct H.
    - apply Choose.LastSteps.Nil.
      now apply last_step.
    - apply (Choose.LastSteps.Cons _ _ (fun a => compile (k a))).
      + now apply step.
      + intro.
        now apply last_traces.
  Qed.*)
End Sound.
