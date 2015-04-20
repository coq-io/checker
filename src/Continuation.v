Require Import ErrorHandlers.All.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module C.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Choose : t E A -> t E A -> t E A
  | Join : forall (B C : Type), t E B -> t E C -> (B * C -> t E A) -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Choose {E A} _ _.
  Arguments Join {E A B C} _ _ _.
End C.

(*Module LastStep.
  Inductive t {E : Effect.t} {A : Type} : C.t E A -> A -> Prop :=
  | Ret : forall (v : A), t (C.Ret v) v
  | ChooseLeft : forall (x1 x2 : C.t E A) (v : A),
    t x1 v ->
    t (C.Choose x1 x2) v
  | ChooseRight : forall (x1 x2 : C.t E A) (v : A),
    t x2 v ->
    t (C.Choose x1 x2) v
  | Join : forall B C (x : C.t E B) (v_x : B) (y : C.t E C) (v_y : C) k v,
    t (A := B) x v_x -> t (A := C) y v_y -> t (k (v_x, v_y)) v ->
    t (C.Join x y k) v.

  Definition inversion_ret {E A} (v v' : A) (H : t (C.Ret (E := E) v) v')
    : v = v' :=
    match H in t x v'' return
      match x with
      | C.Ret v''' => v''' = v''
      | _ => True
      end : Prop with
    | Ret v'' => eq_refl
    | _ => I
    end.

  (*Fixpoint eval {E A} (x : C.t E A) : option A :=
    match x with
    | C.Ret v => Some v
    | C.Call 
    end.*)
End LastStep.*)

Module Location.
  Inductive t : Set :=
  | Call : t
  | ChooseLeft : t -> t
  | ChooseRight : t -> t
  | JoinLeft : t -> t
  | JoinRight : t -> t
  | Join : t -> t.

  Module Valid.
    Inductive t {E A} : Location.t -> C.t E A -> Prop :=
    | Call : forall c h, t Location.Call (C.Call c h)
    | ChooseLeft : forall l (x1 x2 : C.t E A),
      t l x1 ->
      t (Location.ChooseLeft l) (C.Choose x1 x2)
    | ChooseRight : forall l (x1 x2 : C.t E A),
      t l x2 ->
      t (Location.ChooseRight l) (C.Choose x1 x2)
    | JoinLeft : forall l B C (x : C.t E B) (y : C.t E C) k,
      t (A := B) l x ->
      t (Location.JoinLeft l) (C.Join x y k)
    | JoinRight : forall l B C (x : C.t E B) (y : C.t E C) k,
      t (A := C) l y ->
      t (Location.JoinRight l) (C.Join x y k)
    | Join : forall l B C (v_x : B) (v_y : C) k,
      t l (k (v_x, v_y)) ->
      t (Location.Join l) (C.Join (C.Ret v_x) (C.Ret v_y) k).
  End Valid.

  Fixpoint step {E A} (l : t) (x : C.t E A) (H : Valid.t l x)
    : {c : Effect.command E & Effect.answer E c -> C.t E A}.
    destruct l; destruct x as [v | c h | x1 x2 | B C x y k];
      try (assert False by inversion H; tauto).
    - exists c.
      exact h.
    - apply (step _ _ l x1).
      exact (
        match H in Valid.t l x return
          match l with
          | ChooseLeft l =>
            match x with
            | C.Choose x1 _ => Valid.t l x1
            | _ => False
            end
          | _ => True
          end : Prop with
        | Valid.ChooseLeft _ _ _ H => H
        | _ => I
        end).
    - apply (step _ _ l x2).
      exact (
        match H in Valid.t l x return
          match l with
          | ChooseRight l =>
            match x with
            | C.Choose _ x2 => Valid.t l x2
            | _ => False
            end
          | _ => True
          end : Prop with
        | Valid.ChooseRight _ _ _ H => H
        | _ => I
        end).
    - refine (let (c, x') := step _ _ l x _ in _).
      + exact (
          match H in Valid.t l x return
            match l with
            | JoinLeft l =>
              match x with
              | C.Join _ _ x _ _ => Valid.t l x
              | _ => False
              end
            | _ => True
            end : Prop with
          | Valid.JoinLeft _ _ _ _ _ _ H => H
          | _ => I
          end).
      + exists c.
        intro a.
        exact (C.Join (x' a) y k).
    - refine (let (c, y') := step _ _ l y _ in _).
      + exact (
          match H in Valid.t l x return
            match l with
            | JoinRight l =>
              match x with
              | C.Join _ _ _ y _ => Valid.t l y
              | _ => False
              end
            | _ => True
            end : Prop with
          | Valid.JoinRight _ _ _ _ _ _ H => H
          | _ => I
          end).
      + exists c.
        intro a.
        exact (C.Join x (y' a) k).
    - destruct x as [v_x | | |]; try (assert False by inversion H; tauto).
      destruct y as [v_y | | |]; try (assert False by inversion H; tauto).
      apply (step _ _ l (k (v_x, v_y))).
      exact (
        match H in Valid.t l x return
          match l with
          | Join l =>
            match x with
            | C.Join _ _ (C.Ret v_x) (C.Ret v_y) k => Valid.t l (k (v_x, v_y))
            | _ => False
            end
          | _ => True
          end : Prop with
        | Valid.Join _ _ _ _ _ _ H => H
        | _ => I
        end).
  Defined.

  Fixpoint option_step {E A} (l : Location.t) (x : C.t E A)
    : option {c : Effect.command E & Effect.answer E c -> C.t E A} :=
    match l with
    | Call =>
      match x with
      | C.Call c h => Some (existT _ c (fun (a : Effect.answer E c) => h a))
      | _ => None
      end
    | ChooseLeft l =>
      match x with
      | C.Choose x1 _ => option_step l x1
      | _ => None
      end
    | ChooseRight l =>
      match x with
      | C.Choose _ x2 => option_step l x2
      | _ => None
      end
    | JoinLeft l =>
      match x with
      | C.Join _ _ x y k =>
        Option.bind (option_step l x) (fun x' =>
        let (c, f) := x' in
        Some (existT _ c (fun (a : Effect.answer E c) =>
          C.Join (f a) y k)))
      | _ => None
      end
    | JoinRight l =>
      match x with
      | C.Join _ _ x y k =>
        Option.bind (option_step l y) (fun y' =>
        let (c, f) := y' in
        Some (existT _ c (fun (a : Effect.answer E c) =>
          C.Join x (f a) k)))
      | _ => None
      end
    | Join l =>
      match x with
      | C.Join _ _ (C.Ret v_x) (C.Ret v_y) k => option_step l (k (v_x, v_y))
      | _ => None
      end
    end.

  (*Fixpoint option_step_ok {E A} (l : Location.t) (x : C.t E A) {struct l}
    : forall (H : Valid.t l x), option_step l x = Some (step l x H).
    destruct l; destruct x as [v | c h | x1 x2 | B C x y k];
      intro H; try (assert False by inversion H; tauto);
      simpl.
    - reflexivity.
    - apply option_step_ok.
    - apply option_step_ok.
    - refine (
        match option_step l x as x' with
        | Some (existT c f) => _
        | None => _
        end).
      destruct (option_step l x); simpl.
      +

  Qed.*)
End Location.

Module Step.
  Inductive t {E A} (c : Effect.command E)
    : Location.t -> C.t E A -> (Effect.answer E c -> C.t E A) -> Prop :=
  | Call : forall h, t c Location.Call (C.Call c h) h
  | ChooseLeft : forall l (x1 x2 : C.t E A) x1',
    t c l x1 x1' ->
    t c (Location.ChooseLeft l) (C.Choose x1 x2) x1'
  | ChooseRight : forall l (x1 x2 : C.t E A) x2',
    t c l x2 x2' ->
    t c (Location.ChooseRight l) (C.Choose x1 x2) x2'
  | JoinLeft : forall l B C (x : C.t E B) (y : C.t E C) k x',
    t (A := B) c l x x' ->
    t c (Location.JoinLeft l) (C.Join x y k) (fun a => C.Join (x' a) y k)
  | JoinRight : forall l B C (x : C.t E B) (y : C.t E C) k y',
    t (A := C) c l y y' ->
    t c (Location.JoinRight l) (C.Join x y k) (fun a => C.Join x (y' a) k)
  | Join : forall l B C (v_x : B) (v_y : C) k z,
    t c l (k (v_x, v_y)) z ->
    t c (Location.Join l) (C.Join (C.Ret v_x) (C.Ret v_y) k) z.
End Step.
