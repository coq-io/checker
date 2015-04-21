(** * Like `C.t` but without `Let`. *)
Require Import Io.All.

Inductive t (E : Effect.t) (A : Type) : Type :=
| Ret : A -> t E A
| Call : forall c, (Effect.answer E c -> t E A) -> t E A
| Choose : t E A -> t E A -> t E A
| Join : forall (B C : Type), t E B -> t E C -> (B * C -> t E A) -> t E A.
Arguments Ret {E A} _.
Arguments Call {E A} _ _.
Arguments Choose {E A} _ _.
Arguments Join {E A B C} _ _ _.
