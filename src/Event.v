Require Import Io.All.

Record t (E : Effect.t) : Type := New {
  c : Effect.command E;
  a : Effect.answer E c }.
Arguments c {E} _.
Arguments a {E} _.
