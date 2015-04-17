Require Import Io.All.

Record t (E : Effect.t) : Type := New {
  c : Effect.command E;
  a : Effect.answer E c }.
Arguments New {E} _ _.
Arguments c {E} _.
Arguments a {E} _.
