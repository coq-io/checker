Require Import Io.All.
Require Choose.
Require Compile.
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

  (*Fixpoint to_c {E A} {x : C.t E A} {trace}
    (H : Choose.Trace.Partial.t (Compile.to_choose x) trace)
    : C.Trace.Partial.t (Compile.to_choose x) (Trace.to_choose trace).*)
End Partial.
