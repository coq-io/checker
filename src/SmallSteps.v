Require Import Coq.Lists.List.
Require Import Io.All.
Require Choose.

Import ListNotations.
Import C.Notations.
Local Open Scope type.

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
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> Type :=
  | Call : forall c (a : Effect.answer E c), t (C.Call c)
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B),
    t x ->
    t (C.Let _ _ x f)
  | LetDone : forall A B (x : C.t E A) (v : A) (f : A -> C.t E B),
    LastStep.t x v -> t (f v) ->
    t (C.Let _ _ x f)
  | ChooseLeft : forall A (x1 x2 : C.t E A),
    t x1 ->
    t (C.Choose _ x1 x2)
  | ChooseRight : forall A (x1 x2 : C.t E A),
    t x2 ->
    t (C.Choose _ x1 x2)
  | JoinLeft : forall A B (x : C.t E A) (y : C.t E B),
    t x ->
    t (C.Join _ _ x y)
  | JoinRight : forall A B (x : C.t E A) (y : C.t E B),
    t y ->
    t (C.Join _ _ x y).

  Fixpoint eval {E A} {x : C.t E A} (H : t x) : C.t E A :=
    match H with
    | Call _ a => C.Ret _ a
    | Let _ _ _ f H_x => C.Let _ _ (eval H_x) f
    | LetDone _ _ _ _ _ _ H_f => eval H_f
    | ChooseLeft _ _ _ H_x1 => eval H_x1
    | ChooseRight _ _ _ H_x2 => eval H_x2
    | JoinLeft _ _ _ y H_x => C.Join _ _ (eval H_x) y
    | JoinRight _ _ x _ H_y => C.Join _ _ x (eval H_y)
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

Module Complete.
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
    Fixpoint step {E A} (x : C.t E A) (v : A)
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

  Definition any {A : Type} : A.
  Admitted.

  Fixpoint step {E A} (x : C.t E A) (H : Choose.Step.t (compile x)) : Step.t x.
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
    - apply any.
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
End Sound.
