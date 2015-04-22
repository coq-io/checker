Require Import Coq.Lists.List.
Require Import Io.All.
Require Choose.

Import ListNotations.
Import C.Notations.
Local Open Scope type.

Module Last.
  Module Path.
    Inductive t : Set :=
    | Ret : t
    | Let : t -> t -> t
    | ChooseLeft : t -> t
    | ChooseRight : t -> t
    | Join : t -> t -> t.

    Module Eval.
      Inductive t {E : Effect.t}
        : forall {A : Type}, Path.t -> C.t E A -> A -> Prop :=
      | Ret : forall A (v : A), t Path.Ret (C.Ret _ v) v
      | Let : forall A B p_x x (v_x : A) p_f f (v_f : B),
        t p_x x v_x -> t p_f (f v_x) v_f ->
        t (Path.Let p_x p_f) (C.Let _ _ x f) v_f
      | ChooseLeft : forall A p_x1 x1 (v_x1 : A) x2,
        t p_x1 x1 v_x1 -> t (Path.ChooseLeft p_x1) (C.Choose _ x1 x2) v_x1
      | ChooseRight : forall A x1 p_x2 x2 (v_x2 : A),
        t p_x2 x2 v_x2 -> t (Path.ChooseRight p_x2) (C.Choose _ x1 x2) v_x2
      | Join : forall A B p_x x (v_x : A) p_y y (v_y : B),
        t p_x x v_x -> t p_y y v_y ->
        t (Path.Join p_x p_y) (C.Join _ _ x y) (v_x, v_y).
    End Eval.
  End Path.
End Last.

Module Step.
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

(*Module LastSteps.
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
End Steps.*)

Fixpoint compile {E A} (x : C.t E A) : Choose.t E A :=
  match x with
  | C.Ret _ v => Choose.Ret v
  | C.Call c => Choose.Call c Choose.Ret
  | C.Let _ _ x f => Choose.bind (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => Choose.Choose (compile x1) (compile x2)
  | C.Join _ _ x y => Choose.join (compile x) (compile y)
  end.

(*Module Complete.
  Module Last.
    Fixpoint step {E A} (x : C.t E A) (v : A) (H : LastStep.t x v)
      : Choose.LastStep.t (compile x) v.
      destruct H.
      - apply Choose.LastStep.Ret.
      - apply (Choose.Complete.Last.bind _ v_x).
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
    Defined.
  End Last.

  Fixpoint step {E A} (x : C.t E A) (H : Step.t x)
    : Choose.Step.t (compile x).
    destruct H.
    - exact (Choose.Step.Call c _ a).
    - apply Choose.Complete.bind_right.
      now apply step.
    - apply (Choose.Complete.bind_left _ v).
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
  Defined.

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
    Fixpoint step {E A} {x : C.t E A} {v : A}
      (H : Choose.LastStep.t (compile x) v) : LastStep.t x v.
      destruct x; simpl in H.
      - inversion_clear H.
        apply LastStep.Ret.
      - inversion_clear H.
      - destruct (Choose.Sound.Last.bind _ _ _ H) as [v_x H_x].
        destruct H_x.
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
    Defined.
  End Last.

  Fixpoint step {E A} {x : C.t E A} (H : Choose.Step.t (compile x)) : Step.t x.
    destruct x as [v | c | A B x f | A x1 x2 | A B x y]; simpl in H.
    - inversion H.
    - apply Step.Call.
      exact (
        match H in Choose.Step.t x return
          match x with
          | Choose.Call c _ => Effect.answer E c
          | _ => unit
          end with
        | Choose.Step.Call _ _ a => a
        | _ => tt
        end).
    - destruct (Choose.Sound.bind H) as [[v [H_x H_f]] | H_x].
      + eapply Step.LetDone.
        * apply (Last.step H_x).
        * now apply step.
      + apply Step.Let.
        now apply step.
    - inversion_clear H as [| x1_ x2_ H_x1 | x1_ x2_ H_x2].
      + apply Step.ChooseLeft.
        now apply step.
      + apply Step.ChooseRight.
        now apply step.
    - inversion_clear H as [| x1_ x2_ H_x1 | x1_ x2_ H_x2].
      + destruct (Choose.Sound.join_left H_x1) as [H_x | H_y].
        * apply Step.JoinLeft.
          now apply step.
        * apply Step.JoinRight.
          now apply step.
      + destruct (Choose.Sound.join_right H_x2) as [H_x | H_y].
        * apply Step.JoinLeft.
          now apply step.
        * apply Step.JoinRight.
          now apply step.
  Defined.

  Fixpoint step_event {E A} (x : C.t E A) (H : Choose.Step.t (compile x))
    : Step.event (step H) = Choose.Step.event H.
    destruct x; simpl.
  Qed.
End Sound.*)
