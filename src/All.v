Require Import Io.All.

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> bool;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.

Module Choose.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Choose : t E A -> t E A -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Choose {E A} _ _.

  Module Mix.
    Inductive t {E A} : Choose.t E A -> Choose.t E A -> Type :=
    | RetRet : forall v_x v_y, t (Ret v_x) (Ret v_y)
    | RetCall : forall v_x c_y h_y, t (Ret v_x) (Call c_y h_y)
    | RetChoose : forall v_x y1 y2, t (Ret v_x) (Choose y1 y2)
    | CallRet : forall c_x h_x v_y, t (Call c_x h_x) (Ret v_y)
    | CallCall : forall c_x h_x c_y h_y,
      (forall a, t (h_x a) (Call c_y h_y)) ->
      (forall a, t (Call c_x h_x) (h_y a)) ->
      t (Call c_x h_x) (Call c_y h_y)
    | CallChoose : forall c_x h_x y1 y2,
      t (Call c_x h_x) y1 -> t (Call c_x h_x) y2 ->
      t (Call c_x h_x) (Choose y1 y2)
    | ChooseRet : forall x1 x2 v_y, t (Choose x1 x2) (Ret v_y)
    | ChooseCall : forall x1 x2 c_y h_y,
      t x1 (Call c_y h_y) -> t x2 (Call c_y h_y) ->
      t (Choose x1 x2) (Call c_y h_y)
    | ChooseChoose : forall x1 x2 y1 y2,
      t x1 y1 -> t x1 y2 -> t x2 y1 -> t x2 y2 ->
      t (Choose x1 x2) (Choose y1 y2).
    Arguments RetRet {E A} _ _.
    Arguments RetCall {E A} _ _ _.
    Arguments RetChoose {E A} _ _ _.
    Arguments CallRet {E A} _ _ _.
    Arguments CallCall {E A c_x h_x c_y h_y} _ _.
    Arguments CallChoose {E A c_x h_x y1 y2} _ _.
    Arguments ChooseRet {E A} _ _ _ .
    Arguments ChooseCall {E A x1 x2 c_y h_y} _ _.
    Arguments ChooseChoose {E A x1 x2 y1 y2} _ _ _ _.
  End Mix.
End Choose.
