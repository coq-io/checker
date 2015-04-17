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
  Inductive t {E : Effect.t} (c : Effect.command E)
    : forall {A}, C.t E A -> (Effect.answer E c -> C.t E A) -> Prop :=
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

Module Steps.
  Inductive t {E : Effect.t} {A : Type} (x : C.t E A)
    : Trace.t E (C.t E A) -> Prop :=
  | Nil : t x (Trace.Ret x)
  | Cons : forall c k trace,
    Step.t c x k -> (forall a, t (k a) (trace a)) ->
    t x (Trace.Call c trace).
End Steps.

Module LastSteps.
  Inductive t {E : Effect.t} {A : Type} (x : C.t E A) : Trace.t E A -> Prop :=
  | Nil : forall v, LastStep.t x v -> t x (Trace.Ret v)
  | Cons : forall c k trace,
    Step.t c x k -> (forall a, t (k a) (trace a)) ->
    t x (Trace.Call c trace).
End LastSteps.

Module DeadLockFree.
  Definition t {E S} (m : Model.t E S) (s : S) {A} (x : C.t E A) : Prop :=
    forall trace s' x', Steps.t x trace -> NotStuck.t m s trace s' x' ->
    exists trace', exists s'', exists v,
      LastSteps.t x' trace' /\ NotStuck.t m s' trace s'' v.
End DeadLockFree.

Fixpoint compile {E A} (x : C.t E A) : Choose.t E A :=
  match x with
  | C.Ret _ v => Choose.Ret v
  | C.Call c => Choose.Call c Choose.Ret
  | C.Let _ _ x f => Choose.bind (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => Choose.Choose (compile x1) (compile x2)
  | C.Join _ _ x y => Choose.join (compile x) (compile y)
  end.

Module Equiv.
  Fixpoint last_step {E A} (x : C.t E A) (v : A) (H : LastStep.t x v)
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
  Qed.

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
  Qed.

  Fixpoint traces {E A} (x : C.t E A) trace (H : Steps.t x trace)
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
  Qed.
End Equiv.

Module Reverse.
  Fixpoint last_step {E A} (x : C.t E A) (v : A)
    (H : Choose.LastStep.t (compile x) v) : LastStep.t x v.
    destruct x; simpl in H.
    - inversion_clear H.
      apply LastStep.Ret.
    - inversion_clear H.
    - destruct (Choose.Reverse.bind_last _ _ _ H) as [v_x H_x].
      apply (LastStep.Let _ _ _ _ v_x).
      + now apply last_step.
      + now apply last_step.
    - destruct (Choose.Reverse.choose_last H).
      + apply LastStep.ChooseLeft.
        now apply last_step.
      + apply LastStep.ChooseRight.
        now apply last_step.
    - destruct v as [v_x v_y].
      destruct (Choose.Reverse.join_last H).
      apply LastStep.Join.
      + now apply last_step.
      + now apply last_step.
  Qed.

  Fixpoint step {E} c {A} (x : C.t E A) k
    (H : Choose.Step.t c (compile x) (fun a => compile (k a))) : Step.t c x k.
    (*inversion H.*)
    destruct x as [v | c' h | x f | x1 x2 | x y]; simpl in H.
    - inversion H.
    - inversion_clear H.
      apply Step.Call.
  Qed.

  Fixpoint last_traces {E A} (x : C.t E A) (trace : Trace.t E A)
    (H : Choose.LastSteps.t (compile x) trace) : LastSteps.t x trace.
    destruct H.
    - apply Choose.LastSteps.Nil.
      now apply last_step.
    - apply (Choose.LastSteps.Cons _ _ (fun a => compile (k a))).
      + now apply step.
      + intro.
        now apply last_traces.
  Qed.
End Reverse.

Lemma dead_lock {E S} (m : Model.t E S) (s : S) {A} (x : C.t E A)
  (H : Choose.DeadLockFree.t m s (compile x)) : DeadLockFree.t m s x.
  intros trace s' x' H_trace H_not_stuck.
  Check H _ _ _ (traces _ _ H_trace).
  exists
Qed.
