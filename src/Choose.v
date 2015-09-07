Require Import Io.All.

Inductive t (E : Effect.t) (A : Type) : Type :=
| Ret : A -> t E A
| Call : forall c, (Effect.answer E c -> t E A) -> t E A
| Choose : t E A -> t E A -> t E A.
Arguments Ret {E A} _.
Arguments Call {E A} _ _.
Arguments Choose {E A} _ _.

Module Eq.
  Inductive t {E A} : Choose.t E A -> Choose.t E A -> Prop :=
  | Ret : forall v, t (Ret v) (Ret v)
  | Call : forall c h1 h2,
    (forall a, t (h1 a) (h2 a)) -> t (Call c h1) (Call c h2)
  | Choose : forall x11 x12 x21 x22,
    t x11 x12 -> t x21 x22 -> t (Choose x11 x21) (Choose x12 x22).

  Fixpoint reflexivity {E A} (x : Choose.t E A) : t x x.
    destruct x as [v | c h | x1 x2].
    - apply Ret.
    - apply Call; intro a; apply reflexivity.
    - apply Choose; apply reflexivity.
  Qed.
End Eq.

Fixpoint map {E A B} (x : t E A) (f : A -> B) : t E B :=
  match x with
  | Ret v => Ret (f v)
  | Call c h => Call c (fun a => map (h a) f)
  | Choose x1 x2 => Choose (map x1 f) (map x2 f)
  end.

(*Fixpoint map_compose {E A B C} (x : t E A) (f : A -> B) (g : B -> C)
  {struct x} : map (map x f) g = map x (fun x => g (f x)).
Admitted.
(*  destruct x; simpl.
  - reflexivity.
  - apply f_equal.
    rewrite (map_compose _ _ _ _ (t0 a).
Qed.*)*)

Fixpoint bind {E A B} (x : t E A) (f : A -> t E B) : t E B :=
  match x with
  | Ret v => f v
  | Call c h => Call c (fun a => bind (h a) f)
  | Choose x1 x2 => Choose (bind x1 f) (bind x2 f)
  end.

Fixpoint map_eq_bind_ret {E A B} (x : t E A) (f : A -> B) {struct x}
  : Eq.t (map x f) (bind x (fun v_x => Ret (f v_x))).
  destruct x as [v | c h | x1 x2]; simpl.
  - apply Eq.Ret.
  - apply Eq.Call; intro a; apply map_eq_bind_ret.
  - apply Eq.Choose; apply map_eq_bind_ret.
Qed.

Fixpoint join_left_aux {E A B} (x : t E A) (y : t E B)
  (join_right : forall A, t E A -> t E (A * B)) : t E (A * B) :=
  match x with
  | Ret v => map y (fun y => (v, y))
  | Call c h =>
    Call c (fun a =>
      Choose (join_left_aux (h a) y join_right) (join_right _ (h a)))
  | Choose x1 x2 =>
    Choose (join_left_aux x1 y join_right) (join_left_aux x2 y join_right)
  end.

Fixpoint join_right {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  match y with
  | Ret v => map x (fun x => (x, v))
  | Call c h =>
    Call c (fun a =>
      Choose (join_left_aux x (h a) (fun _ x => join_right x (h a)))
        (join_right x (h a)))
  | Choose y1 y2 => Choose (join_right x y1) (join_right x y2)
  end.

Definition join_left {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  join_left_aux x y (fun _ x => join_right x y).

Definition join {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  Choose (join_left x y) (join_right x y).
