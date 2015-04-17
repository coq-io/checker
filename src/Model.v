Require Import Io.All.

Record t (E : Effect.t) (S : Type) := New {
  pre : Effect.command E -> S -> Prop;
  answer : forall c s, pre c s -> Effect.answer E c;
  state : forall c s, pre c s -> S }.
Arguments New {E S} _ _ _.
Arguments pre {E S} _ _ _.
Arguments answer {E S} _ _ _ _.
Arguments state {E S} _ _ _ _.

Module Dec.
  Definition t {E S} (m : Model.t E S) : Type :=
    forall c s, {Model.pre m c s} + {~ Model.pre m c s}.
End Dec.
