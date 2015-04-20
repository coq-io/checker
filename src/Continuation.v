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

Module LastStep.
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
End LastStep.

Module Location.
  Inductive t : Set :=
  | Call : t
  | ChooseLeft : t -> t
  | ChooseRight : t -> t
  | JoinLeft : t -> t
  | JoinRight : t -> t
  | Join : t -> t.

  Module Valid.
    Inductive t {E A} (c : Effect.command E) : Location.t -> C.t E A -> Prop :=
    | Call : forall h, t c Location.Call (C.Call c h)
    | ChooseLeft : forall l (x1 x2 : C.t E A),
      t c l x1 ->
      t c (Location.ChooseLeft l) (C.Choose x1 x2)
    | ChooseRight : forall l (x1 x2 : C.t E A),
      t c l x2 ->
      t c (Location.ChooseRight l) (C.Choose x1 x2)
    | JoinLeft : forall l B C (x : C.t E B) (y : C.t E C) k,
      t (A := B) c l x ->
      t c (Location.JoinLeft l) (C.Join x y k)
    | JoinRight : forall l B C (x : C.t E B) (y : C.t E C) k,
      t (A := C) c l y ->
      t c (Location.JoinRight l) (C.Join x y k)
    | Join : forall l B C (x : C.t E B) v_x (y : C.t E C) v_y k,
      LastStep.t x v_x -> LastStep.t y v_y ->
      t c l (k (v_x, v_y)) ->
      t c (Location.Join l) (C.Join x y k).

    Definition inversion_call {E A} {c l c' h}
      (H : t c l (C.Call (E := E) (A := A) c' h)) : c = c'.
      now inversion_clear H.
    Qed.
  End Valid.

  Fixpoint step {E A} c (l : t) (x : C.t E A) (a : Effect.answer E c) (H : Valid.t c l x) {struct l} : C.t E A.
    destruct l; destruct x as [v | c' h | x1 x2 | B C x y k];
      try (assert False by inversion H; tauto).
    - rewrite (Valid.inversion_call H) in a.
      exact (h a).
    - refine (C.Choose _ x2).
      apply (step _ _ c l x1 a).
      now inversion H.
    - refine (C.Choose x1 _).
      apply (step _ _ c l x2 a).
      now inversion H.
    - refine (C.Join _ y k).
      apply (step _ _ c l x a).
      exact (
        match H in Valid.t _ l x return
          match l with
          | Location.JoinLeft l =>
            match x with
            | C.Join _ _ x _ _  => Valid.t c l x
            | _ => False
            end
          | _ => True
          end : Prop with
        | Valid.JoinLeft _ _ _ _ _ _ H => H
        | _ => I
        end).
    - refine (C.Join x _ k).
      apply (step _ _ c l y a).
      exact (
        match H in Valid.t _ l x return
          match l with
          | Location.JoinRight l =>
            match x with
            | C.Join _ _ _ y _  => Valid.t c l y
            | _ => False
            end
          | _ => True
          end : Prop with
        | Valid.JoinRight _ _ _ _ _ _ H => H
        | _ => I
        end).
    - exact (
      refine (
        match H in Valid.t _ l x return
          match l with
          | Location.JoinRight l =>
            match x with
            | C.Join _ _ _ y _  => Valid.t c l y
            | _ => False
            end
          | _ => True
          end : Prop with
        | Valid.JoinRight _ _ _ _ _ _ H => H
        | _ => I
        end).
      
  Defined.
End Location.
