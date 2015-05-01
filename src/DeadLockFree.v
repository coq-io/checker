Require Import Io.All.
Require Model.
Require Import Semantics.

Module C.
  Module DeadLockFree.
    Inductive t {E S A} (m : Model.t E S) (s : S) (x : C.t E A) : Prop :=
    | New :
      (exists p, exists v, C.Last.Eval.t p x v) \/
        (exists c, exists x', exists s', C.Step.t m c s x x' s') ->
      (forall c x' s', C.Step.t m c s x x' s' -> t m s' x') ->
      t m s x.
  End DeadLockFree.
End C.

Module Choose.
  Module DeadLockFree.
    Inductive t {E S A} (m : Model.t E S) (s : S) (x : Choose.t E A) : Prop :=
    | New :
      (exists p, exists v, Choose.Last.Eval.t p x v) \/
        (exists c, exists x', exists s', Choose.Step.t m c s x x' s') ->
      (forall c x' s', Choose.Step.t m c s x x' s' -> t m s' x') ->
      t m s x.
  End DeadLockFree.
End Choose.
