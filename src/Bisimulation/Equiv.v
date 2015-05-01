Require Import Io.All.
Require Choose.
Require Compile.
Require Import DeadLockFree.
Require Import Semantics.
Require ToChoose.
Require ToC.

Fixpoint to_c {E S A} {m : Model.t E S} {s : S} {x : C.t E A}
  (H : Choose.DeadLockFree.t m s (Compile.to_choose x))
  : C.DeadLockFree.t m s x.
  destruct H as [H H_next].
  apply C.DeadLockFree.New.
  - destruct H as [[p [v H]] | [c [x' [s' H]]]].
    + left.
      destruct (ToC.Last.to_c Choose.Path.Done H) as [p' [H_p' H_x]].
      now exists p', v.
    + right.
      inversion_clear H.
      destruct (ToC.to_c H1) as [p' [x'' [H_p [H_x'' H_x]]]].
      exists c, x'', s'.
      now apply (C.Step.New m c s x x'' p' a s').
  - clear H; intros c x'' s' H_x.
    apply to_c.
    apply (H_next c).
    destruct H_x.
    eapply (Choose.Step.New m c s _ _ _ a s').
    * exact H.
    * eapply ToChoose.to_choose.
      exact H0.
Qed.
