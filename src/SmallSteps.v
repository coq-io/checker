Require Import Coq.Lists.List.
Require Import Io.All.
Require Choose.

Import ListNotations.
Import C.Notations.
Local Open Scope type.

(*Module Value.
  Fixpoint eval {E : Effect.t} {A : Type} (x : C.t E A) : option A :=
    match x with
    | C.Ret _ v => 
    end.

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
End Value.*)

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

Module Eval.
  Module Choose.
    Inductive t : Set :=
    | Abort
    | Choose.

    Definition answer (c : t) : Type :=
      match c with
      | Abort => Empty_set
      | Choose => bool 
      end.

    Definition E : Effect.t :=
      Effect.New t answer.

    Definition abort {A : Type} : C.t E A :=
      let! x := call E Abort in
      match x with end.

    Definition choose : C.t E bool :=
      call E Choose.
  End Choose.

  Fixpoint eval {E : Effect.t} {A : Type} (x : C.t E A) : C.t Choose.E A :=
    match x with
    | C.Ret _ v => ret v
    | C.Call _ => Choose.abort
    | C.Let _ _ x f =>
      let! x := eval x in
      eval (f x)
    | C.Choose _ x1 x2 =>
      let! choice := Choose.choose in
      if choice then
        eval x1
      else
        eval x2
    | C.Join _ _ x y =>
      let! x := eval x in
      let! y := eval y in
      ret (x, y)
    end.
End Eval.

Module Denotation.
  Module Choice.
    Inductive t (A : Type) : Type :=
    | Ret : A -> t A
    | Bind : forall B, t B -> (B -> t A) -> t A
    | Choose : t A -> t A -> t A.
    Arguments Ret {A} _.
    Arguments Bind {A B} _ _.
    Arguments Choose {A} _ _.

    (*Fixpoint flatten {A : Type} (c : t (option A)) : option (t A) :=
      match c with
      | Ret None => None
      | Ret (Some v) => Some (Ret v)
      | Bind c f => Bind (flatten c) (fun v => flatten (f v))
      | Choose c1 c2 =>
        match flatten c1 with
        | None => flatten c2
        | Some c1 =>
          match flatten c2 with
          | None => Some c1
          | Some c2 => Some (Choose c1 c2)
          end
        end
      end.*)

    (*Fixpoint bind {A B : Type} (x : t (option A)) (f : A -> t (option B))
      : t (option B) :=
      match x with
      | Ret None => Ret None
      | Ret (Some v) => f v
      | Choose
      end.*)
  End Choice.

  Fixpoint values {E A} (x : C.t E A) : Choice.t (option A) :=
    match x with
    | C.Ret _ v => Choice.Ret (Some v)
    | C.Call _ => Choice.Ret None
    | C.Let _ _ x f => Choice.Bind (values x) (fun v => values (f v))
    | _ => Choice.Ret None
    end.

  Module Value.
    Inductive t : Type -> Type :=
    | Ret : forall A (v : A), t A.

    Definition gre {E} (c : Effect.command E) a (H : LastStep.t (C.Call c) a)
      : forall {A : Type}, A :=
      match match H in LastStep.t x v return
        (match x with
        | C.Call _ => False
        | _ => True
        end) : Prop with
      | LastStep.Ret _ _ => I
      | LastStep.Let _ _ _ _ _ _ _ _ => I
      | LastStep.ChooseLeft _ _ _ _ _ => I
      | LastStep.ChooseRight _ _ _ _ _ => I
      | LastStep.Join _ _ _ _ _ _ _ _ => I
      end with end.

    Fixpoint compile {E A} (x : C.t E A) {struct x}
      : forall v, LastStep.t x v -> t A.
      refine (
        match x return
          match x with
          | C.Ret _ _ => forall v, LastStep.t (C.Ret _ v) v -> t A
          | C.Let _ _ x f => forall v, LastStep.t (C.Let _ _ x f) v -> t A
          | _ => forall v, LastStep.t x v -> t A
          end with
        | C.Ret _ _ => fun v _ => Ret _ v
        | C.Call c => fun _ H =>
          match
            match H in LastStep.t x v return
              match x with
              | C.Call _ => False
              | _ => True
              end : Prop with
            | LastStep.Ret _ _ => I
            | LastStep.Let _ _ _ _ _ _ _ _ => I
            | LastStep.ChooseLeft _ _ _ _ _ => I
            | LastStep.ChooseRight _ _ _ _ _ => I
            | LastStep.Join _ _ _ _ _ _ _ _ => I
            end with
          end
        | C.Let _ _ x f => fun v H =>
          compile (f v) _
        end).
      Show.
  End Value.
End Denotation.

(*Module Gre.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> Type :=
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B),
    t x ->
    t (C.Let _ _ x f)
  | Ret : forall A (v : A), t (C.Ret _ v).

  Module Inversion.
    Definition gre {E A B} (x : C.t E A) (f : A -> C.t E B)
      (H : t (C.Let _ _ x f)) : t x :=
      match H with
      | Let _ _ _ _ H => H
      end.

    Lemma gre {E A B} (x : C.t E A) (f : A -> C.t E B) (H : t (C.Let _ _ x f))
      : t x.
      inversion H.
    Qed.
  End Inversion.
End Gre.*)

(*Module Location.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> Type :=
  | Call : forall c,
    t (C.Call c)
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

  Fixpoint command {E A} {x : C.t E A} (l : t x) : Effect.command E :=
    match l with
    | Call c => c
    | 
    end.

  Fixpoint run {E A} {c : Effect.command E} {x : C.t E A} (l : t c x)
    (a : Effect.answer E c) : C.t E A :=
    match l with
    | Call => C.Ret _ a
    | Let _ _ _ f l_x => C.Let _ _ (run l_x a) f
    | LetDone _ _ _ _ _ _ l_f_x => run l_f_x a
    | ChooseLeft _ x1 _ l_x2 => C.Choose _ x1 (run l_x2 a)
    | ChooseRight _ _ x2 l_x1 => C.Choose _ (run l_x1 a) x2
    | JoinLeft _ _ _ y l_x => C.Join _ _ (run l_x a) y
    | JoinRight _ _ x _ l_y => C.Join _ _ x (run l_y a)
    end.

  Module Inversion.
    (*Lemma ret {E A} {v : A} (l : t (C.Ret E v)) : False.
      inversion H.
    Qed.

    Lemma call {E} {c : Effect.command E} {x'} (H : t (C.Call c) x')
      : exists a, x' = C.Ret _ a.
      inversion_clear H.
      eexists.
      reflexivity.
    Qed.*)

    Lemma let_ {E A B} {c : Effect.command E} {x : C.t E A} {f : A -> C.t E B}
      (l : t c (C.Let _ _ x f))
      : t c x + {v : A & LastStep.t x v * t c (f v)}.
      inversion l.
      admit.
      admit.
(*      inversion H.
      - left.
        eexists.
        split.
        + trivial.
        + admit.
      - right.
        admit.*)
    Qed.
  End Inversion.
End Location.

Module Step.
  Inductive t {E : Effect.t} {A : Type} (x : C.t E A) : C.t E A -> Prop :=
  | New : forall c (l : Location.t c x) a, t x (Location.run l a).
End Step.*)

(*Module Step.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> Type :=
  | Call : forall c, Effect.answer E c -> t (C.Call c)
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

  Fixpoint run {E A} {x : C.t E A} (step : t x) : C.t E A :=
    match step with
    | Call c a => C.Ret _ a
    | Let _ _ _ f step_x => C.Let _ _ (run step_x) f
    | LetDone _ _ _ _ _ _ step_f_x => run step_f_x
    | ChooseLeft _ x1 _ step_x2 => C.Choose _ x1 (run step_x2)
    | ChooseRight _ _ x2 step_x1 => C.Choose _ (run step_x1) x2
    | JoinLeft _ _ _ y step_x => C.Join _ _ (run step_x) y
    | JoinRight _ _ x _ step_y => C.Join _ _ x (run step_y)
    end.

  Module Inversion.
    Lemma ret {E A} {v : A} (H : t (C.Ret E v)) : False.
      inversion H.
    Qed.

    Lemma let_ {E A B} {x : C.t E A} {f : A -> C.t E B} (H : t (C.Let _ _ x f))
      : (exists x', t x x' /\ y = C.Let _ _ x' f) \/
        (exists v, LastStep.t x v /\ t (f v) y).
      inversion H.
      - left.
        eexists.
        split.
        + trivial.
        + admit.
      - right.
        admit.
    Qed.
  End Inversion.
End Step.*)

(*Module Step.
  Inductive t {E : Effect.t}
    : forall {A}, C.t E A -> C.t E A -> Prop :=
  | Call : forall c a, t (C.Call c) (C.Ret _ a)
  | Let : forall A B (x x' : C.t E A) (f : A -> C.t E B),
    t x x' ->
    t (C.Let _ _ x f) (C.Let _ _ x' f)
  | LetDone : forall A B (x : C.t E A) (v : A) (f : A -> C.t E B) (y : C.t E B),
    LastStep.t x v -> t (f v) y ->
    t (C.Let _ _ x f) y
  | ChooseLeft : forall A (x1 x2 x1' : C.t E A),
    t x1 x1' ->
    t (C.Choose _ x1 x2) x1'
  | ChooseRight : forall A (x1 x2 x2' : C.t E A),
    t x2 x2' ->
    t (C.Choose _ x1 x2) x2'
  | JoinLeft : forall A B (x x' : C.t E A) (y : C.t E B),
    t x x' ->
    t (C.Join _ _ x y) (C.Join _ _ x' y)
  | JoinRight : forall A B (x : C.t E A) (y y' : C.t E B),
    t y y' ->
    t (C.Join _ _ x y) (C.Join _ _ x y').

  (*Module Inversion.
    Lemma ret {E A} {v : A} {x'} (H : t (C.Ret E v) x') : False.
      inversion H.
    Qed.

    Lemma call {E} {c : Effect.command E} {x'} (H : t (C.Call c) x')
      : exists a, x' = C.Ret _ a.
      inversion_clear H.
      eexists.
      reflexivity.
    Qed.

    Lemma let_ {E A B} {x : C.t E A} {f : A -> C.t E B} {y}
      (H : t (C.Let _ _ x f) y)
      : (exists x', t x x' /\ y = C.Let _ _ x' f) \/
        (exists v, LastStep.t x v /\ t (f v) y).
      inversion H.
      - left.
        eexists.
        split.
        + trivial.
        + admit.
      - right.
        admit.
    Qed.
  End Inversion.*)
End Step.*)

Module Schedule.
  Inductive t (A : Type) : Type :=
  | Ret : A -> t A
  | Choose : (bool -> t A) -> t A.
End Schedule.

Module Denotation.
  Inductive t {E : Effect.t} (A : Type) : Type :=
  | Ret : A -> t A
  | Call : Schedule.t {c : Effect.command E & Effect.answer E c -> t A} -> t A.
End Denotation.

Module Location.
  Inductive t : Set :=
  | Call : t
  | Let : t -> t
  | LetDone : t -> t
  | ChooseLeft : t -> t
  | ChooseRight : t -> t
  | JoinLeft : t -> t
  | JoinRight : t -> t.

  Module Valid.
    Inductive t {E : Effect.t} (c : Effect.command E)
      : Location.t -> forall {A}, C.t E A -> Prop :=
    | Call : t c Location.Call (C.Call c)
    | Let : forall l A B (x : C.t E A) (f : A -> C.t E B),
      t c l x -> t c (Location.Let l) (C.Let _ _ x f)
    | LetDone : forall l A B (x : C.t E A) (v : A) (f : A -> C.t E B),
      LastStep.t x v -> t c l (f v) -> t c (Location.LetDone l) (C.Let _ _ x f)
    | ChooseLeft : forall l A (x1 x2 : C.t E A),
      t c l x1 -> t c (Location.ChooseLeft l) (C.Choose _ x1 x2)
    | ChooseRight : forall l A (x1 x2 : C.t E A),
      t c l x2 -> t c (Location.ChooseRight l) (C.Choose _ x1 x2)
    | JoinLeft : forall l A B (x : C.t E A) (y : C.t E B),
      t c l x -> t c (Location.JoinLeft l) (C.Join _ _ x y)
    | JoinRight : forall l A B (x : C.t E A) (y : C.t E B),
      t c l y -> t c (Location.JoinRight l) (C.Join _ _ x y).
  End Valid.
End Location.

Module Step.
  Fixpoint step {E} (c : Effect.command E) (l : Location.t)
    (a : Effect.answer E c) {struct l}
    : forall {A} {x : C.t E A}, Location.Valid.t c l x -> C.t E A :=
    (*destruct l; intros A x H.
    - inversion H.
  Defined.*)
    match l return
      match l with
      | Location.Call => C.t E (Effect.answer E c)
      end with
    | Location.Call => fun _ _ _ => C.Ret E a
    end.
End Step.

(*Module Location.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> Type :=
  | Call : forall c, t (C.Call c)
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

  Fixpoint command {E A} {x : C.t E A} (l : t x) : Effect.command E :=
    match l with
    | Call c => c
    | Let _ _ _ _ l | LetDone _ _ _ _ _ _ l
      | ChooseLeft _ _ _ l | ChooseRight _ _ _ l
      | JoinLeft _ _ _ _ l | JoinRight _ _ _ _ l => command l
    end.

  Fixpoint reduce {E A} {x : C.t E A} (l : t x)
    (a : Effect.answer E (command l)) {struct l} : C.t E A.
    destruct l.
    - exact (C.Ret _ a).
    - exact (C.Let _ _ (reduce _ _ _ l a) f).
    - exact (reduce _ _ _ l a).
    - exact (reduce _ _ _ l a).
    - exact (reduce _ _ _ l a).
    - exact (C.Join _ _ (reduce _ _ _ l a) y).
    - exact (C.Join _ _ x (reduce _ _ _ l a)).
  Defined.

  Module Inversion.
    Definition ret {E A} {v : A} (l : t (C.Ret E v)) : False :=
      match l with
      end.
    Print ret.

    Definition call {E} {c : Effect.command E} (l : t (C.Call c)) : nat :=
      match l with
      | Call _ => 12
      (* | Let _ _ _ _ _ => tt *)
      end.

    Definition call' {E} {c : Effect.command E} (l : t (C.Call c)) : nat :=
      match l in t x return match x with C.Call _ => nat | _ => unit end with
      | Call _ => 12
      | _ => tt
      end.
  End Inversion.
End Location.

Module Step.
  Inductive t {E : Effect.t} {A : Type} (x : C.t E A) : C.t E A -> Prop :=
  | New : forall (l : Location.t x) (a : Effect.answer E (Location.command l)),
    t x (Location.reduce l a).

  (*Module Inversion.
    Definition call {E c} (H : t (C.Call c))
  End Inversion.*)
End Step.*)

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

(*Module Compile.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> Type :=
  | Ret : forall A (v : A), t (C.Ret _ v)
  | Call : forall c, t (C.Call c)
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B),
    t x -> (forall v_x, t (f v_x)) ->
    t (C.Let _ _ x f)
  | Choose : forall A (x1 x2 : C.t E A),
    t x1 -> t x2 ->
    t (C.Choose _ x1 x2)
  | Join : forall A B (x : C.t E A) (y : C.t E B),
    .
End Compile.*)

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

  Fixpoint step {E A} (x x' : C.t E A) (H : Step.t x x')
    : Choose.Step.t (compile x) (compile x').
    destruct H.
    - exact (Choose.Step.Call _ _ _).
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
End Complete.*)

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

  Definition gre {E A} {x : C.t E A} {v : A} (H : compile x = Choose.Ret v)
    : x = C.Ret E v.
    destruct x; simpl in H; try congruence.
  Admitted.

  (*Fixpoint step {E A} (x x' : C.t E A)
    (H : Choose.Step.t (compile x) (compile x')) : Step.t x x'.
    (*case_eq x.*)
    (* destruct e. *)
    destruct x as [v | c | x f | x1 x2 | x y]; simpl in H.
    - inversion H.
    - destruct (Choose.Sound.call H).
      rewrite (gre e).
      apply Step.Call.
    - 
      assert (x' = C.Ret _ x) by admit.
      rewrite H0.
      
      destruct x'.
      inversion x'.
      inversion H.
      assert (e' : Event.t E) by admit.
      assert (e = e') by admit.
      rewrite H0.
      rewrite <- H1.
 assert (exists a, x' = C.Ret _ a).
      admit.
      destruct H0.
      rewrite H0.
      apply Step.Call.
  Defined.*)

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
