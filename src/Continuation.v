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
End LastStep.

Module Step.
  Inductive t {E A} (c : Effect.command E) (a : Effect.answer E c)
    : C.t E A -> Prop :=
  | Call : forall h, t c a (C.Call c h)
  | ChooseLeft : forall (x1 x2 : C.t E A),
    t c a x1 ->
    t c a (C.Choose x1 x2)
  | ChooseRight : forall (x1 x2 : C.t E A),
    t c a x2 ->
    t c a (C.Choose x1 x2)
  | JoinLeft : forall B C (x : C.t E B) (y : C.t E C) k,
    t (A := B) c a x ->
    t c a (C.Join x y k)
  | JoinRight : forall B C (x : C.t E B) (y : C.t E C) k,
    t (A := C) c a y ->
    t c a (C.Join x y k)
  | Join : forall B C (x : C.t E B) v_x (y : C.t E C) v_y k,
    LastStep.t x v_x -> LastStep.t y v_y -> t c a (k (v_x, v_y)) ->
    t c a (C.Join x y k).

  Definition inversion_call_c {E A} c a c' h
    (H : t c a (C.Call (E := E) (A := A) c' h)) : c = c'.
    now inversion_clear H.
  Qed.
End Step.
