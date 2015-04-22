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
    Fixpoint to_choose (p : C.Last.Path.t) : Choose.Last.Path.t :=
      match p with
      | C.Last.Path.Ret => Choose.Last.Path.Ret
      | C.Last.Path.Let p_x p_f =>
        Choose.Last.Path.bind (to_choose p_x) (to_choose p_f)
      | C.Last.Path.ChooseLeft p_x1 =>
        Choose.Last.Path.ChooseLeft (to_choose p_x1)
      | C.Last.Path.ChooseRight p_x2 =>
        Choose.Last.Path.ChooseRight (to_choose p_x2)
      | C.Last.Path.Join p_x p_y =>
        Choose.Last.Path.bind (to_choose p_x) (to_choose p_y)
      end.
  End Last.
End Path.
