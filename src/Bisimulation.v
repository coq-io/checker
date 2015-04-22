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
End ToChoose.
