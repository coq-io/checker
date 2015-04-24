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
        Choose.Last.Path.join (to_choose p_x) (to_choose p_y)
      end.

    Fixpoint to_c {E A} (x : C.t E A) (p : Choose.Last.Path.t)
      : option (C.Last.Path.t * A * Choose.Last.Path.t) :=
      match x with
      | C.Ret _ v => Some (C.Last.Path.Ret, v, p)
      | C.Call _ => None
      | C.Let _ _ x f =>
        match to_c x p with
        | None => None
        | Some (p_x, v_x, p) =>
          match to_c (f v_x) p with
          | None => None
          | Some (p_f, v_y, p) => Some (C.Last.Path.Let p_x p_f, v_y, p)
          end
        end
      | C.Choose _ x1 x2 =>
        match p with
        | Choose.Last.Path.Ret => None
        | Choose.Last.Path.ChooseLeft p =>
          match to_c x1 p with
          | None => None
          | Some (p_x1, v_x1, p) => Some (C.Last.Path.ChooseLeft p_x1, v_x1, p)
          end
        | Choose.Last.Path.ChooseRight p =>
          match to_c x2 p with
          | None => None
          | Some (p_x2, v_x2, p) => Some (C.Last.Path.ChooseRight p_x2, v_x2, p)
          end
        end
      | C.Join _ _ x y =>
        match p with
        | Choose.Last.Path.Ret => None
        | Choose.Last.Path.ChooseLeft p =>
          match to_c x p with
          | None => None
          | Some (p_x, v_x, p) =>
            match to_c y p with
            | None => None
            | Some (p_y, v_y, p) =>
              Some (C.Last.Path.Join p_x p_y, (v_x, v_y), p)
            end
          end
        | Choose.Last.Path.ChooseRight p =>
          match to_c y p with
          | None => None
          | Some (p_y, v_y, p) =>
            match to_c x p with
            | None => None
            | Some (p_x, v_x, p) =>
              Some (C.Last.Path.Join p_x p_y, (v_x, v_y), p)
            end
          end
        end
      end.
  End Last.

  Fixpoint to_choose (p : C.Path.t) : Choose.Path.t :=
    match p with
    | C.Path.Call => Choose.Path.Call
    | C.Path.Let p_x => to_choose p_x
    | C.Path.LetDone p_x p_f =>
      Choose.Path.bind (Last.to_choose p_x) (to_choose p_f)
    | C.Path.ChooseLeft p_x1 => Choose.Path.ChooseLeft (to_choose p_x1)
    | C.Path.ChooseRight p_x2 => Choose.Path.ChooseRight (to_choose p_x2)
    | C.Path.JoinLeft p_x => Choose.Path.ChooseLeft (to_choose p_x)
    | C.Path.JoinRight p_y => Choose.Path.ChooseRight (to_choose p_y)
    end.

  Fixpoint to_c {E A} (x : C.t E A) (p : Choose.Last.Path.t)
    : (C.Last.Path.t * A * Choose.Last.Path.t) + C.Path.t :=
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
      | inr p_x => inr p_x
      end
    | C.Choose _ x1 x2 =>
      match p with
      | Choose.Last.Path.Ret => inr C.Path.Call
      | Choose.Last.Path.ChooseLeft p =>
        match to_c x1 p with
        | inl (p_x1, v_x1, p) => inl (C.Last.Path.ChooseLeft p_x1, v_x1, p)
        | inr p_x1 => inr p_x1
        end
      | Choose.Last.Path.ChooseRight p =>
        match to_c x2 p with
        | inl (p_x2, v_x2, p) => inl (C.Last.Path.ChooseRight p_x2, v_x2, p)
        | inr p_x2 => inr p_x2
        end
      end
    | C.Join _ _ x y =>
      match p with
      | Choose.Last.Path.Ret => inr C.Path.Call
      | Choose.Last.Path.ChooseLeft p =>
        match to_c x p with
        | inl (p_x, v_x, p) =>
          match to_c y p with
          | inl (p_y, v_y, p) => inl (C.Last.Path.Join p_x p_y, (v_x, v_y), p)
          | inr p_y => inr p_y
          end
        | inr p_x => inr p_x
        end
      | Choose.Last.Path.ChooseRight p =>
        match to_c y p with
        | inl (p_y, v_y, p) =>
          match to_c x p with
          | inl (p_x, v_x, p) => inl (C.Last.Path.Join p_x p_y, (v_x, v_y), p)
          | inr p_x => inr p_x
          end
        | inr p_y => inr p_y
        end
      end
    end.
End Path.
