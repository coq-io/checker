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
  destruct H.
  - destruct (ToC.Last.to_c Choose.Path.Done H) as [p' [H_p' H_x]].
    eapply C.DeadLockFree.Ret.
    exact H_x.
  - inversion_clear H.
    destruct (ToC.to_c H2) as [p' [x'' [H_p [H_x'' H_x]]]].
    eapply C.DeadLockFree.Call.
    + now apply (C.Step.New m c s x x'' p' a s').
    + clear c x'' a s' H1 H2 H_x H_x'' H_p.
      intros c x'' s' H_x.
      apply to_c.
      apply (H0 c).
      destruct H_x.
      eapply (Choose.Step.New m c s _ _ _ a s').
      * exact H.
      * eapply ToChoose.to_choose.
        exact H1.
Qed.
