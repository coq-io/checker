Require Import Io.All.
Require Choose.
Require Compile.
Require DeadLockFree.
Require Import Semantics.
Require ToChoose.
Require ToC.
Require Trace.

Module Trace.
  Fixpoint to_choose {E A} (trace : Trace.t E (C.t E A))
    : Trace.t E (Choose.t E A) :=
    match trace with
    | Trace.Ret x => Trace.Ret (Compile.to_choose x)
    | Trace.Call c k => Trace.Call c (fun a => to_choose (k a))
    end.
End Trace.

Module Partial.
  Module NotStuck.
    Fixpoint to_choose {E S A} {m : Model.t E S} {s : S}
      {trace : Trace.t E (C.t E A)} {s' : S} {x' : C.t E A}
      (H : DeadLockFree.NotStuck.t m s trace s' x')
      : DeadLockFree.NotStuck.t m s (Trace.to_choose trace) s'
        (Compile.to_choose x').
      inversion_clear H.
      - apply DeadLockFree.NotStuck.Ret.
      - apply (DeadLockFree.NotStuck.Call m s s' _ c _ H0).
        now apply to_choose.
    Qed.
  End NotStuck.

  Fixpoint to_choose {E A} {x : C.t E A} {trace} (H : C.Trace.Partial.t x trace)
    : Choose.Trace.Partial.t (Compile.to_choose x) (Trace.to_choose trace).
    inversion_clear H.
    - apply Choose.Trace.Partial.Ret.
    - apply Choose.Trace.Partial.Call.
      intros p a x' H.
      destruct (ToC.to_c H) as [p' [x'' [H_p' [H_x'' H']]]].
      rewrite <- H_x''.
      apply to_choose.
      now apply (H0 p').
  Qed.
End Partial.

Module Total.
  Fixpoint to_c {E A} {x : C.t E A} {trace}
    (H : Choose.Trace.Total.t (Compile.to_choose x) trace)
    : C.Trace.Total.t x trace.
    inversion_clear H.
    - destruct (ToC.Last.to_c Choose.Path.Done H0) as [p' [H_p' H_x]].
      now apply (C.Trace.Total.Ret _ p').
    - apply C.Trace.Total.Call.
      intros p a x' H_x.
      apply to_c.
      apply (H0 (Compile.Path.to_choose p)).
      now apply ToChoose.to_choose.
  Qed.
End Total.

Module DeadLockFree.
  Lemma to_c {E S A} {m : Model.t E S} {s : S} {x : C.t E A}
    (H : DeadLockFree.Choose.t m s (Compile.to_choose x))
    : DeadLockFree.C.t m s x.
    intros trace s' x' H_trace H_not_stuck.
    destruct (H (Trace.to_choose trace) s' (Compile.to_choose x')
      (Partial.to_choose H_trace) (Partial.NotStuck.to_choose H_not_stuck))
      as [trace' [s'' [v [H'_trace H'_not_stuck]]]].
    exists trace', s'', v.
    split.
    - now apply Total.to_c.
    - exact H'_not_stuck.
  Qed.
