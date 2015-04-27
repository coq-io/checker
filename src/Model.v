Require Import Io.All.

Definition t (E : Effect.t) (S : Type) : Type :=
  forall (c : Effect.command E), S -> option (Effect.answer E c * S).
