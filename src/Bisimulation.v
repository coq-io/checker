Require Import Io.All.
Require Choose.
Require Compile.
Require Import Semantics.

Module ToChoose.
  Module Last.
    Fixpoint bind {E A B} {p_x x} {v_x : A} {p_f f} {v_f : B}
      (H_x : C.Last.Eval.t p_x x v_x) (H_f : C.Last.Eval.t p_f (f v_x) v_f)
      : Choose.Last.Eval.t (E := E)
        (Choose.Last.Path.bind
          (Compile.Path.Last.to_choose p_x)
          (Compile.Path.Last.to_choose p_f))
        (Choose.bind (Compile.to_choose x) (fun v => Compile.to_choose (f v)))
        v_f.
    Admitted.

    Fixpoint to_choose {E A} {p : C.Last.Path.t} {x : C.t E A} {v : A}
      (H : C.Last.Eval.t p x v)
      : Choose.Last.Eval.t
        (Compile.Path.Last.to_choose p) (Compile.to_choose x) v.
      destruct H; simpl.
      - apply Choose.Last.Eval.Ret.
      - now apply (bind H).
      - apply Choose.Last.Eval.ChooseLeft.
        now apply to_choose.
      - apply Choose.Last.Eval.ChooseRight.
        now apply to_choose.
      - induction p_x; simpl.
        + refine (
            match H in C.Last.Eval.t p x v_x return
              match p with
              | C.Last.Path.Ret =>
                match x with
                | C.Ret _ _ =>
                  Choose.Last.Eval.t (Compile.Path.Last.to_choose p_y)
  (Choose.join (Compile.to_choose x) (Compile.to_choose y)) (v_x, v_y)
                | _ =>
                  Choose.Last.Eval.t (Compile.Path.Last.to_choose p_y)
    (Choose.join (Compile.to_choose x) (Compile.to_choose y)) (v_x, v_y)
                end
              | _ => True
              end : Prop with
            | C.Last.Eval.Ret _ _ => _
            | _ => I
            end).
        + apply H.
        + apply H0.
      - 
    Qed.
  End Last.
End ToChoose.
