Require Import Io.All.
Require Choose.
Require Compile.
Require Import Semantics.

Module ToChoose.
  Module Last.
    Fixpoint map {E A B} {p x} {f : A -> B} (s : Choose.Last.Start.t p x)
      : Choose.Last.Start.t (E := E) p (Choose.map x f).
    Admitted.

    Fixpoint bind {E A B} {p_x x} {v_x} {p_f f}
      (s_x : Choose.Last.Start.t (A := A) p_x x)
      (s_f : Choose.Last.Start.t (A := B) p_f (f v_x))
      : Choose.Last.Start.t (E := E) (Choose.Last.Path.bind p_x p_f)
        (Choose.bind x f).
    Admitted.

    Fixpoint join {E A B} {p_x} {x : Choose.t E A} {p_y} {y : Choose.t E B}
      (s_x : Choose.Last.Start.t p_x x) (s_y : Choose.Last.Start.t p_y y)
      : Choose.Last.Start.t (Choose.Last.Path.bind p_x p_y) (Choose.join x y).
    Admitted.

    Fixpoint bind' {E A B} {p_x x v_x} {p_f f}
      (s_x : C.Last.Start.t p_x x) (s_f : C.Last.Start.t p_f (f v_x))
      : Choose.Last.Start.t
        (Choose.Last.Path.bind
          (Compile.Path.Last.to_choose p_x) (Compile.Path.Last.to_choose p_f))
        (Choose.bind (E := E) (A := A) (B := B)
          (Compile.to_choose x) (fun v => Compile.to_choose (f v))).
    Admitted.

    Fixpoint to_choose {E A} {p : C.Last.Path.t} {x : C.t E A}
      (s : C.Last.Start.t p x)
      : Choose.Last.Start.t
        (Compile.Path.Last.to_choose p) (Compile.to_choose x).
      destruct s; simpl.
      - apply Choose.Last.Start.Ret.
      - apply (bind (v_x := v_x)).
        + now apply to_choose.
        + now apply to_choose.
      - apply Choose.Last.Start.ChooseLeft.
        now apply to_choose.
      - apply Choose.Last.Start.ChooseRight.
        now apply to_choose.
      - apply join.
        + now apply to_choose.
        + now apply to_choose.
    Qed.
  End Last.
End ToChoose.
