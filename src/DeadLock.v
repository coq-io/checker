Require Choose.
Require Model.
Require Trace.

Module NotStuck.
  Inductive t {E S T} (m : Model.t E S) : S -> Trace.t E T -> S -> T -> Prop :=
  | Ret : forall s x, t m s (Trace.Ret x) s x
  | Call : forall s s' x c k (H : Model.pre m c s),
    t m (Model.state m c s H) (k (Model.answer m c s H)) s' x ->
    t m s (Trace.Call c k) s' x.
End NotStuck.

Module Choose.
  Module DeadLockFree.
    Definition t {E S} (m : Model.t E S) (s : S) {A} (x : t E A) : Prop :=
      forall trace s' x', Steps.t x trace -> NotStuck.t m s trace s' x' ->
      exists trace', exists s'', exists v,
        LastSteps.t x' trace' /\ NotStuck.t m s' trace s'' v.
  End DeadLockFree.
End Choose.
