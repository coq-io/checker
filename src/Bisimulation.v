Require Import Io.All.
Require Choose.
Require Compile.
Require Import Semantics.

Module ToChoose.
  Module Last.
    Fixpoint map {E A B} {p_x x v_x} {f : A -> B}
      (H : Choose.Last.Eval.t p_x x v_x)
      : Choose.Last.Eval.t (E := E) p_x (Choose.map x f) (f v_x).
      destruct H; simpl.
      - apply Choose.Last.Eval.Ret.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply map.
      - apply Choose.Last.Eval.ChooseRight.
        now apply map.
    Qed.

    Fixpoint bind {E A B} {p_x x} {v_x : A} {p_f f} {v_f : B}
      (H_x : Choose.Last.Eval.t p_x x v_x)
      (H_f : Choose.Last.Eval.t p_f (f v_x) v_f)
      : Choose.Last.Eval.t (E := E) (Choose.Last.Path.bind p_x p_f)
        (Choose.bind x f) v_f.
      destruct H_x; simpl.
      - exact H_f.
      - apply Choose.Last.Eval.ChooseLeft.
        eapply bind.
        + exact H_x.
        + exact H_f.
      - apply Choose.Last.Eval.ChooseRight.
        eapply bind.
        + exact H_x.
        + exact H_f.
    Qed.

    Fixpoint join_left {E A B} {p_x x} {v_x : A} {p_y y} {v_y : B}
      (H_x : Choose.Last.Eval.t p_x x v_x) (H_y : Choose.Last.Eval.t p_y y v_y)
      : Choose.Last.Eval.t (E := E)
        (Choose.Last.Path.bind p_x p_y) (Choose.join_left x y) (v_x, v_y).
      destruct H_x; unfold Choose.join_left; simpl.
      - now apply map.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply join_left.
      - apply Choose.Last.Eval.ChooseRight.
        now apply join_left.
    Qed.

    Definition join {E A B} {p_x x} {v_x : A} {p_y y} {v_y : B}
      (H_x : Choose.Last.Eval.t p_x x v_x) (H_y : Choose.Last.Eval.t p_y y v_y)
      : Choose.Last.Eval.t (E := E)
        (Choose.Last.Path.join p_x p_y) (Choose.join x y) (v_x, v_y).
      apply Choose.Last.Eval.ChooseLeft.
      destruct H_x; simpl.
      - now apply map.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply join_left.
      - apply Choose.Last.Eval.ChooseRight.
        now apply join_left.
    Qed.

    Fixpoint to_choose {E A} {p : C.Last.Path.t} {x : C.t E A} {v : A}
      (H : C.Last.Eval.t p x v)
      : Choose.Last.Eval.t
        (Compile.Path.Last.to_choose p) (Compile.to_choose x) v.
      destruct H; simpl.
      - apply Choose.Last.Eval.Ret.
      - apply (bind (v_x := v_x)).
        + now apply to_choose.
        + now apply to_choose.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply to_choose.
      - apply Choose.Last.Eval.ChooseRight.
        now apply to_choose.
      - apply join.
        + now apply to_choose.
        + now apply to_choose.
    Qed.
  End Last.

  Fixpoint bind {E c a A B} {p_x : Choose.Path.t} {x x' f}
    (H : Choose.Eval.t (E := E) (A := A) c a p_x x x')
    : Choose.Eval.t (A := B) c a p_x (Choose.bind x f) (Choose.bind x' f).
  Admitted.

  Fixpoint bind_done {E c a A B} {p_x x v p_f f y}
    (H_x : Choose.Last.Eval.t (E := E) (A := A) p_x x v)
    (H_f : Choose.Eval.t (E := E) (A := B) c a p_f (f v) y)
    : Choose.Eval.t c a (Choose.Path.bind p_x p_f) (Choose.bind x f) y.
  Admitted.

  Fixpoint join_left {E c a A B} {p_x} {x x' : Choose.t E A} {y : Choose.t E B}
    (H : Choose.Eval.t c a p_x x x')
    : Choose.Eval.t c a p_x (Choose.join_left x y) (Choose.join x' y).
  Admitted.

  Fixpoint join_right {E c a A B} {x : Choose.t E B} {p_y}
    {y y' : Choose.t E A} (H : Choose.Eval.t c a p_y y y')
    : Choose.Eval.t c a p_y (Choose.join_right x y) (Choose.join x y').
  Admitted.

  Fixpoint to_choose {E c a A} {p : C.Path.t} {x x' : C.t E A}
    (H : C.Eval.t c a p x x')
    : Choose.Eval.t c a
      (Compile.Path.to_choose p) (Compile.to_choose x) (Compile.to_choose x').
    destruct H; simpl.
    - apply Choose.Eval.Call.
    - apply bind.
      now apply to_choose.
    - apply (bind_done (v := v_x)).
      + now apply Last.to_choose.
      + now apply to_choose.
    - apply Choose.Eval.ChooseLeft.
      now apply to_choose.
    - apply Choose.Eval.ChooseRight.
      now apply to_choose.
    - apply Choose.Eval.ChooseLeft.
      apply join_left.
      now apply to_choose.
    - apply Choose.Eval.ChooseRight.
      apply join_right.
      now apply to_choose.
  Qed.
End ToChoose.
