Require Import Io.All.
Require Model.
Require Import Semantics.
Require Trace.

Module NotStuck.
  Inductive t {E S T} (m : Model.t E S) : S -> Trace.t E T -> S -> T -> Prop :=
  | Ret : forall s x, t m s (Trace.Ret x) s x
  | Call : forall s s' x c k (H : Model.pre m c s),
    t m (Model.state m c s H) (k (Model.answer m c s H)) s' x ->
    t m s (Trace.Call c k) s' x.
End NotStuck.

Module C.
  Definition t {E S A} (m : Model.t E S) (s : S) (x : C.t E A) : Prop :=
    forall trace s' x', C.Trace.Partial.t x trace ->
      NotStuck.t m s trace s' x' -> exists trace', exists s'', exists v,
      C.Trace.Total.t x' trace' /\ NotStuck.t m s' trace s'' v.
End C.

Module Choose.
  Definition t {E S A} (m : Model.t E S) (s : S) (x : Choose.t E A) : Prop :=
    forall trace s' x', Choose.Trace.Partial.t x trace ->
      NotStuck.t m s trace s' x' -> exists trace', exists s'', exists v,
      Choose.Trace.Total.t x' trace' /\ NotStuck.t m s' trace s'' v.
End Choose.
