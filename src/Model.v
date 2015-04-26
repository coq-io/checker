Require Import Io.All.

Record t (E : Effect.t) (S : Type) := New {
  pre : Effect.command E -> S -> Prop;
  answer : forall c s, pre c s -> Effect.answer E c;
  state : forall c s, pre c s -> S;
  pre_answer_constant : forall c s H1 H2, answer c s H1 = answer c s H2;
  pre_state_constant : forall c s H1 H2, state c s H1 = state c s H2 }.
Arguments New {E S} _ _ _ _ _.
Arguments pre {E S} _ _ _.
Arguments answer {E S} _ _ _ _.
Arguments state {E S} _ _ _ _.
Arguments pre_answer_constant {E S} _ _ _ _ _.
Arguments pre_state_constant {E S} _ _ _ _ _.

Module Dec.
  Definition t {E S} (m : Model.t E S) : Type :=
    forall c s, {Model.pre m c s} + {~ Model.pre m c s}.
End Dec.
