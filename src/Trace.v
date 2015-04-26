Require Import Io.All.

Inductive t (E : Effect.t) (A : Type) :=
| Ret : A -> t E A
| Call : forall c, (Effect.answer E c -> t E A) -> t E A.
Arguments Ret {E A} _.
Arguments Call {E A} _ _.
