Require Import Io.All.
Require Choose.
Require Import Semantics.

Fixpoint to_choose {E A} (x : C.t E A) : Choose.t E A :=
  match x with
  | C.Ret _ v => Choose.Ret v
  | C.Call c => Choose.Call c Choose.Ret
  | C.Let _ _ x f => Choose.bind (to_choose x) (fun x => to_choose (f x))
  | C.Choose _ x1 x2 => Choose.Choose (to_choose x1) (to_choose x2)
  | C.Join _ _ x y => Choose.join (to_choose x) (to_choose y)
  end.

Module Path.
  Module Last.
    Fixpoint to_choose (p : C.Last.Path.t) : Choose.Path.t :=
      match p with
      | C.Last.Path.Ret => Choose.Path.Done
      | C.Last.Path.Let p_x p_f =>
        Choose.Path.bind (to_choose p_x) (to_choose p_f)
      | C.Last.Path.ChooseLeft p_x1 =>
        Choose.Path.ChooseLeft (to_choose p_x1)
      | C.Last.Path.ChooseRight p_x2 =>
        Choose.Path.ChooseRight (to_choose p_x2)
      | C.Last.Path.Join p_x p_y =>
        Choose.Path.ChooseLeft
          (Choose.Path.bind  (to_choose p_x) (to_choose p_y))
      end.
  End Last.

  Fixpoint to_choose (p : C.Path.t) : Choose.Path.t :=
    match p with
    | C.Path.Call => Choose.Path.Done
    | C.Path.Let p_x => to_choose p_x
    | C.Path.LetDone p_x p_f =>
      Choose.Path.bind (Last.to_choose p_x) (to_choose p_f)
    | C.Path.ChooseLeft p_x1 => Choose.Path.ChooseLeft (to_choose p_x1)
    | C.Path.ChooseRight p_x2 => Choose.Path.ChooseRight (to_choose p_x2)
    | C.Path.JoinLeft p_x => Choose.Path.ChooseLeft (to_choose p_x)
    | C.Path.JoinLeftDone p_x p_y =>
      Choose.Path.ChooseLeft (Choose.Path.bind
        (Last.to_choose p_x) (to_choose p_y))
    | C.Path.JoinRight p_y => Choose.Path.ChooseRight (to_choose p_y)
    end.

  Fixpoint to_c {E A} (x : C.t E A) (p : Choose.Path.t)
    : (C.Last.Path.t * A * Choose.Path.t) + C.Path.t :=
    match x with
    | C.Ret _ v => inl (C.Last.Path.Ret, v, p)
    | C.Call c => inr C.Path.Call
    | C.Let _ _ x f =>
      match to_c x p with
      | inl (p_x, v_x, p) =>
        match to_c (f v_x) p with
        | inl (p_f, v_y, p) => inl (C.Last.Path.Let p_x p_f, v_y, p)
        | inr p_y => inr (C.Path.LetDone p_x p_y)
        end
      | inr p_x => inr (C.Path.Let p_x)
      end
    | C.Choose _ x1 x2 =>
      match p with
      | Choose.Path.Done => inr C.Path.Call
      | Choose.Path.ChooseLeft p =>
        match to_c x1 p with
        | inl (p_x1, v_x1, p) => inl (C.Last.Path.ChooseLeft p_x1, v_x1, p)
        | inr p_x1 => inr (C.Path.ChooseLeft p_x1)
        end
      | Choose.Path.ChooseRight p =>
        match to_c x2 p with
        | inl (p_x2, v_x2, p) => inl (C.Last.Path.ChooseRight p_x2, v_x2, p)
        | inr p_x2 => inr (C.Path.ChooseRight p_x2)
        end
      end
    | C.Join _ _ x y =>
      match p with
      | Choose.Path.Done => inr C.Path.Call
      | Choose.Path.ChooseLeft p =>
        match to_c x p with
        | inl (p_x, v_x, p) =>
          match to_c y p with
          | inl (p_y, v_y, p) => inl (C.Last.Path.Join p_x p_y, (v_x, v_y), p)
          | inr p_y => inr (C.Path.JoinLeftDone p_x p_y)
          end
        | inr p_x => inr (C.Path.JoinLeft p_x)
        end
      | Choose.Path.ChooseRight p =>
        match to_c y p with
        | inl (p_y, v_y, p) =>
          match to_c x p with
          | inl (p_x, v_x, p) => inl (C.Last.Path.Join p_x p_y, (v_x, v_y), p)
          | inr p_x => inr p_x
          end
        | inr p_y => inr (C.Path.JoinRight p_y)
        end
      end
    end.
End Path.
