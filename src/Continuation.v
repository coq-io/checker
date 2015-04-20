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

Module Next.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Call : forall c, (Effect.answer E c -> C.t E A) -> t E A
  | JoinLeft : forall B C, t E B -> C.t E C -> (B * C -> C.t E A) -> t E A
  | JoinRight : forall B C, C.t E B -> t E C -> (B * C -> C.t E A) -> t E A.
  Arguments Call {E A} _ _.
  Arguments JoinLeft {E A B C} _ _ _.
  Arguments JoinRight {E A B C} _ _ _.
End Next.

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
    : option (Next.t E A) :=
    match l with
    | Call =>
      match x with
      | C.Call c h => Some (Next.Call c h)
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
        Some (Next.JoinLeft x' y k))
      | _ => None
      end
    | JoinRight l =>
      match x with
      | C.Join _ _ x y k =>
        Option.bind (option_step l y) (fun y' =>
        Some (Next.JoinRight x y' k))
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
  Inductive t {E A} : Location.t -> C.t E A -> Next.t E A -> Prop :=
  | Call : forall c h, t Location.Call (C.Call c h) (Next.Call c h)
  | ChooseLeft : forall l (x1 x2 : C.t E A) x1',
    t l x1 x1' ->
    t (Location.ChooseLeft l) (C.Choose x1 x2) x1'
  | ChooseRight : forall l (x1 x2 : C.t E A) x2',
    t l x2 x2' ->
    t (Location.ChooseRight l) (C.Choose x1 x2) x2'
  | JoinLeft : forall l B C (x : C.t E B) (y : C.t E C) k x',
    t (A := B) l x x' ->
    t (Location.JoinLeft l) (C.Join x y k) (Next.JoinLeft x' y k)
  | JoinRight : forall l B C (x : C.t E B) (y : C.t E C) k y',
    t (A := C) l y y' ->
    t (Location.JoinRight l) (C.Join x y k) (Next.JoinRight x y' k)
  | Join : forall l B C (v_x : B) (v_y : C) k z,
    t l (k (v_x, v_y)) z ->
    t (Location.Join l) (C.Join (C.Ret v_x) (C.Ret v_y) k) z.

  Fixpoint step_ok {E A} (l : Location.t) (x : C.t E A) (x' : Next.t E A)
    {struct l} : t l x x' -> Location.option_step l x = Some x'.
    destruct l; destruct x as [v | c' h | x1 x2 | B C x y k];
      try (intro H; assert (f : False) by inversion H; destruct f);
      simpl.
    - intro H.
      apply f_equal.
      exact (
        match H in t _ x x' return
          match x with
          | C.Call c' h => Next.Call c' h = x'
          | _ => True
          end : Prop with
        | Call _ _ => eq_refl
        | _ => I
        end).
    - intro H.
      apply step_ok.
      exact (
        match H in t l x x' return
          match l with
          | Location.ChooseLeft l =>
            match x with
            | C.Choose x1 _ => t l x1 x'
            | _ => False
            end
          | _ => True
          end : Prop with
        | ChooseLeft _ _ _ _ H => H
        | _ => I
        end).
    - intro H.
      apply step_ok.
      exact (
        match H in t l x x' return
          match l with
          | Location.ChooseRight l =>
            match x with
            | C.Choose _ x2 => t l x2 x'
            | _ => False
            end
          | _ => True
          end : Prop with
        | ChooseRight _ _ _ _ H => H
        | _ => I
        end).
    - refine (
        match x' with
        | Next.JoinLeft _ _ x' _ _ => fun H => _
        | _ => fun H => match _ : False with end
        end); try (inversion H; tauto).
      refine (
        match H in t l x x' return
          match l with
          | Location.JoinLeft l =>
            match x with
            | C.Join _ _ x y k =>
              match x' with
              | Next.JoinLeft _ _ x' y' k' => Option.bind (Location.option_step l x)
    (fun x' => Some (Next.JoinLeft x' y k)) = Some (Next.JoinLeft x' y' k')
              | _ => Option.bind (Location.option_step l x)
    (fun x' => Some (Next.JoinLeft x' y k)) = Some x'
              end
            | _ => False
            end
          | _ => True
          end : Prop with
        | JoinLeft _ _ _ x _ _ x' H =>
          let H_eq := step_ok _ _ _ x x' H in
          _
        | _ => I
        end).
      now rewrite H_eq.
    - refine (
        match x' with
        | Next.JoinRight _ _ x' _ _ => fun H => _
        | _ => fun H => match _ : False with end
        end); try (inversion H; tauto).
      refine (
        match H in t l x x' return
          match l with
          | Location.JoinRight l =>
            match x with
            | C.Join _ _ x y k =>
              match x' with
              | Next.JoinRight _ _ x' y' k' => Option.bind (Location.option_step l y)
    (fun y' => Some (Next.JoinRight x y' k)) = Some (Next.JoinRight x' y' k')
              | _ => Option.bind (Location.option_step l y)
    (fun y' => Some (Next.JoinRight x y' k)) = Some x'
              end
            | _ => False
            end
          | _ => True
          end : Prop with
        | JoinRight _ _ _ _ y _ y' H =>
          let H_eq := step_ok _ _ _ y y' H in
          _
        | _ => I
        end).
      now rewrite H_eq.
    - intro H.
      destruct x; try (assert (f : False) by inversion H; destruct f).
      destruct y; try (assert (f : False) by inversion H; destruct f).
      apply step_ok.
      refine (
        match H in t l x x' return
          match l with
          | Location.Join l =>
            match x with
            | C.Join _ _ (C.Ret v_x) (C.Ret v_y) k => t l (k (v_x, v_y)) x'
            | _ => False
            end
          | _ => True
          end : Prop with
        | Join _ _ _ _ _ _ _ H => H
        | _ => I
        end).
  Qed.
End Step.
