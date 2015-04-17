Require Import Io.All.

Inductive t (E : Effect.t) (T : Type) : Type :=
| Ret : T -> t E T
| Call : forall c, (Effect.answer E c -> t E T) -> t E T.
Arguments Ret {E T} _.
Arguments Call {E T} _ _.

Fixpoint map {E T1 T2} (f : T1 -> T2) (trace : t E T1) : t E T2 :=
  match trace with
  | Ret x => Ret (f x)
  | Call c k => Call c (fun a => map f (k a))
  end.
