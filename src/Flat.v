(** * Like `C.t` but without `Let`. *)
Require Import Io.All.

Inductive t (E : Effect.t) (A : Type) : Type :=
| Ret : A -> t E A
| Call : forall c, (Effect.answer E c -> t E A) -> t E A
| Choose : t E A -> t E A -> t E A
| Join : forall (B C : Type), t E B -> t E C -> (B -> C -> t E A) -> t E A.
Arguments Ret {E A} _.
Arguments Call {E A} _ _.
Arguments Choose {E A} _ _.
Arguments Join {E A B C} _ _ _.

Module LastStep.
  Inductive t {E : Effect.t} {A : Type} : Flat.t E A -> A -> Type :=
  | Ret : forall (v : A), t (Flat.Ret v) v
  | ChooseLeft : forall (x1 x2 : Flat.t E A) (v : A),
    t x1 v ->
    t (Flat.Choose x1 x2) v
  | ChooseRight : forall (x1 x2 : Flat.t E A) (v : A),
    t x2 v ->
    t (Flat.Choose x1 x2) v
  | Join : forall B C (x : Flat.t E B) (y : Flat.t E C) h v_x v_y v_h,
    t (A := B) x v_x -> t (A := C) y v_y -> t (h v_x v_y) v_h ->
    t (Flat.Join x y h) v_h.
End LastStep.
