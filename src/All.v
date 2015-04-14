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
  | Choose : forall B, t E B -> t E B -> (B -> t E A) -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Choose {E A B} _ _ _.

  Module Mix.
    Inductive t {E A B} : Choose.t E A -> Choose.t E B -> Type :=
    | RetRet : forall v_x v_y, t (Ret v_x) (Ret v_y)
    | RetCall : forall v_x c_y h_y, t (Ret v_x) (Call c_y h_y)
    | RetChoose : forall B' v_x y1 y2 (k_y : B' -> Choose.t E B),
      t (Ret v_x) (Choose y1 y2 k_y)
    | CallRet : forall c_x h_x v_y, t (Call c_x h_x) (Ret v_y)
    | CallCall : forall c_x h_x c_y h_y,
      (forall a, t (h_x a) (Call c_y h_y)) ->
      (forall a, t (Call c_x h_x) (h_y a)) ->
      t (Call c_x h_x) (Call c_y h_y)
    | CallChoose : forall B' c_x h_x y1 y2 (k_y : B' -> Choose.t E B),
      t (B := B') (Call c_x h_x) y1 -> t (B := B') (Call c_x h_x) y2 ->
      t (Call c_x h_x) (Choose y1 y2 k_y)
    | ChooseRet : forall A' x1 x2 (k_x : A' -> Choose.t E A) v_y,
      t (Choose x1 x2 k_x) (Ret v_y)
    | ChooseCall : forall A' x1 x2 (k_x : A' -> Choose.t E A) c_y h_y,
      t (A := A') x1 (Call c_y h_y) -> t (A := A') x2 (Call c_y h_y) ->
      t (Choose x1 x2 k_x) (Call c_y h_y)
    | ChooseChoose : forall A' B' x1 x2 y1 y2
      (k_x : A' -> Choose.t E A) (k_y : B' -> Choose.t E B),
      t (A := A') (B := B') x1 y1 -> t (A := A') (B := B') x1 y2 ->
      t (A := A') (B := B') x2 y1 -> t (A := A') (B := B') x2 y2 ->
      t (Choose x1 x2 k_x) (Choose y1 y2 k_y).
    Arguments RetRet {E A B} _ _.
    Arguments RetCall {E A B} _ _ _.
    Arguments RetChoose {E A B B'} _ _ _ _.
    Arguments CallRet {E A B} _ _ _.
    Arguments CallCall {E A B c_x h_x c_y h_y} _ _.
    Arguments CallChoose {E A B B' c_x h_x y1 y2} _ _ _.
    Arguments ChooseRet {E A B A'} _ _ _ _.
    Arguments ChooseCall {E A B A' x1 x2} _ {c_y h_y} _ _.
    Arguments ChooseChoose {E A B A' B' x1 x2 y1 y2} _ _ _ _ _ _.

    Fixpoint make_call {E A B}
      (c_x : Effect.command E) (h_x : Effect.answer E c_x -> Choose.t E A)
      (y : Choose.t E B) (z : forall y a, t (h_x a) y)
      : t (Choose.Call c_x h_x) y :=
      match y with
      | Ret v_y => CallRet c_x h_x v_y
      | Call c_y h_y =>
        CallCall (z (Call c_y h_y)) (fun a => make_call c_x h_x (h_y a) z)
      | Choose y1 y2 =>
        CallChoose (make_call c_x h_x y1 z) (make_call c_x h_x y2 z)
      end.

    Fixpoint make {E A B} (x : Choose.t E A) (y : Choose.t E B) : t x y :=
      match x with
      | Ret v_x =>
        match y with
        | Ret v_y => RetRet v_x v_y
        | Call c_y h_y => RetCall v_x c_y h_y
        | Choose y1 y2 => RetChoose v_x y1 y2
        end
      | Call c_x h_x => make_call c_x h_x y (fun y a => make (h_x a) y)
      | Choose x1 x2 =>
        match y with
        | Ret v_y => ChooseRet x1 x2 v_y
        | Call c_y h_y =>
          ChooseCall (make x1 (Call c_y h_y)) (make x2 (Call c_y h_y))
        | Choose y1 y2 =>
          ChooseChoose (make x1 y1) (make x1 y2) (make x2 y1) (make x2 y2)
        end
      end.

    Fixpoint join {E A B C} {x y} (xy : t x y) (k : A -> B -> Choose.t E C)
      : Choose.t E C :=
      match xy with
      | RetRet v_x v_y => k v_x v_y
      | RetCall v_x c_y h_y => bind (Call c_y h_y) (fun y => k v_x y)
      | RetChoose v_x y1 y2 => bind (Choose y1 y2) (fun y => k v_x y)
      | CallRet c_x h_x v_y => bind (Call c_x h_x) (fun x => k x v_y)
      | CallCall c_x _ c_y _ m_x m_y =>
        Choose (Call c_x (fun a => join (m_x a) k))
          (Call c_y (fun a => join (m_y a) k))
      | CallChoose _ _ _ _ m_y1 m_y2 => Choose (join m_y1 k) (join m_y2 k)
      | ChooseRet x1 x2 v_y => x1 x2 v_y => bind (Choose x1 x2) 
      end.
  End Mix.
End Choose.
