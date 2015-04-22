Require Import Io.All.
Require Choose.
Require Import SmallSteps.

Module Last.
  Fixpoint map {E A B} (x : Choose.t E A) (v : A) (f : A -> B)
    (H : Choose.LastStep.t x v) : Choose.LastStep.t (Choose.map x f) (f v).
    destruct H.
    - apply Choose.LastStep.Ret.
    - apply Choose.LastStep.ChooseLeft.
      now apply map.
    - apply Choose.LastStep.ChooseRight.
      now apply map.
  Defined.

  Fixpoint bind {E A B} (x : Choose.t E A) (v_x : A) (f : A -> Choose.t E B)
    (v_y : B) (H_x : Choose.LastStep.t x v_x)
    (H_f : Choose.LastStep.t (f v_x) v_y)
    : Choose.LastStep.t (Choose.bind x f) v_y.
    destruct H_x.
    - exact H_f.
    - apply Choose.LastStep.ChooseLeft.
      now apply bind with (v_x := v).
    - apply Choose.LastStep.ChooseRight.
      now apply bind with (v_x := v).
  Defined.

  Fixpoint join_left {E A B} (x : Choose.t E A) (v_x : A) (y : Choose.t E B)
    (v_y : B) (H_x : Choose.LastStep.t x v_x) (H_y : Choose.LastStep.t y v_y)
    : Choose.LastStep.t (Choose.join_left x y) (v_x, v_y).
    destruct H_x.
    - now apply map.
    - apply Choose.LastStep.ChooseLeft.
      now apply join_left.
    - apply Choose.LastStep.ChooseRight.
      now apply join_left.
  Defined.

  Fixpoint step {E A} (x : C.t E A) (v : A) (H : LastStep.t x v)
    : Choose.LastStep.t (compile x) v.
    destruct H.
    - apply Choose.LastStep.Ret.
    - apply (bind _ v_x).
      + now apply step.
      + now apply step.
    - apply Choose.LastStep.ChooseLeft.
      now apply step.
    - apply Choose.LastStep.ChooseRight.
      now apply step.
    - apply Choose.LastStep.ChooseLeft.
      apply join_left.
      + now apply step.
      + now apply step.
  Qed.
End Last.
