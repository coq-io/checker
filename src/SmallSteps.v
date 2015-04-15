Require Import Coq.Lists.List.

Import ListNotations.

Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module Model.
  Record t (E : Effect.t) (S : Type) := New {
    condition : Effect.command E -> S -> Prop;
    answer : forall c, S -> Effect.answer E c;
    state : Effect.command E -> S -> S }.
  Arguments New {E S} _ _ _.
  Arguments condition {E S} _ _ _.
  Arguments answer {E S} _ _ _.
  Arguments state {E S} _ _ _.
End Model.

Module Event.
  Record t (E : Effect.t) := New {
    c : Effect.command E;
    a : Effect.answer E c }.
  Arguments New {E} _ _.
  Arguments c {E} _.
  Arguments a {E} _.
End Event.

Module C.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Join : forall {B C : Type}, t E B -> t E C -> (B * C -> t E A) -> t E A
  | Choose : t E A -> t E A -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Join {E A B C} _ _ _.
  Arguments Choose {E A} _ _.

  Module Step.
    Inductive t {E : Effect.t} {A : Type} (e : Event.t E)
      : C.t E A -> C.t E A -> Type :=
    | Call : forall h,
      t e (C.Call (Event.c e) h) (h (Event.a e))
    | JoinLeft : forall B C (x : C.t E B) (y : C.t E C) h x',
      t e (A := B) x x' ->
      t e (C.Join x y h) (C.Join x' y h)
    | JoinRight : forall B C (x : C.t E B) (y : C.t E C) h y',
      t e (A := C) y y' ->
      t e (C.Join x y h) (C.Join x y' h)
    | Join : forall B C (x : B) (y : C) h,
      t e (C.Join (C.Ret x) (C.Ret y) h) (h (x, y))
    | ChooseLeft : forall x1 x2 x1',
      t e x1 x1' ->
      t e (C.Choose x1 x2) x1'
    | ChooseRight : forall x1 x2 x2',
      t e x2 x2' ->
      t e (C.Choose x1 x2) x2'.
  End Step.

  Module Steps.
    Inductive t {E : Effect.t} {A : Type}
      : list (Event.t E) -> C.t E A -> C.t E A -> Type :=
    | Nil : forall x,
      t [] x x
    | Cons : forall e es x x' x'',
      Step.t e x x' -> t es x' x'' ->
      t (e :: es) x x''.
  End Steps.

  Module ModelStep.
    Inductive t {E : Effect.t} {S : Type} (m : Model.t E S) {A : Type} (s : S)
      : C.t E A -> S -> C.t E A -> Type :=
    | Call : forall c h,
      Model.condition m c s ->
      t m s (C.Call c h) (Model.state m c s) (h (Model.answer m c s))
    | JoinLeft : forall B C (x : C.t E B) (y : C.t E C) h s' x',
      t m (A := B) s x s' x' ->
      t m s (C.Join x y h) s' (C.Join x' y h)
    | JoinRight : forall B C (x : C.t E B) (y : C.t E C) h s' y',
      t m (A := C) s y s' y' ->
      t m s (C.Join x y h) s' (C.Join x y' h)
    | Join : forall B C (x : B) (y : C) h,
      t m s (C.Join (C.Ret x) (C.Ret y) h) s (h (x, y))
    | ChooseLeft : forall x1 x2 s' x1',
      t m s x1 s' x1' ->
      t m s (C.Choose x1 x2) s' x1'
    | ChooseRight : forall x1 x2 s' x2',
      t m s x2 s' x2' ->
      t m s (C.Choose x1 x2) s' x2'.
  End ModelStep.
End C.

Module Choose.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A
  | Choose : forall B, t E B -> t E B -> (B -> t E A) -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
  Arguments Choose {E A B} _ _ _.

  Module Step.
    Inductive t {E : Effect.t} {A : Type} (e : Event.t E)
      : Choose.t E A -> Choose.t E A -> Type :=
    | Call : forall h,
      t e (Choose.Call (Event.c e) h) (h (Event.a e))
    | ChooseLeft : forall x1 x2 k x1',
      t e x1 x1' ->
      t e (Choose.Choose x1 x2 k) x1'
    | ChooseRight : forall x1 x2 k x2',
      t e x2 x2' ->
      t e (Choose.Choose x1 x2 k) x2'.
  End Step.

  Fixpoint bind {E A B} (x : t E A) (f : A -> t E B) : t E B :=
    match x with
    | Ret v_x => f v_x
    | Call c_x h_x => Call c_x (fun a => bind (h_x a) f)
    | Choose _ x1 x2 k_x => Choose x1 x2 (fun x => bind (k_x x) f)
    end.

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
      (y : Choose.t E B) (z : forall B (y : Choose.t E B) a, t (h_x a) y)
      : t (Choose.Call c_x h_x) y :=
      match y with
      | Ret v_y => CallRet c_x h_x v_y
      | Call c_y h_y =>
        CallCall (z _ (Call c_y h_y)) (fun a => make_call c_x h_x (h_y a) z)
      | Choose _ y1 y2 k_y =>
        CallChoose k_y (make_call c_x h_x y1 z) (make_call c_x h_x y2 z)
      end.

    Fixpoint make {E A B} (x : Choose.t E A) (y : Choose.t E B) : t x y :=
      match x with
      | Ret v_x =>
        match y with
        | Ret v_y => RetRet v_x v_y
        | Call c_y h_y => RetCall v_x c_y h_y
        | Choose _ y1 y2 k_y => RetChoose v_x y1 y2 k_y
        end
      | Call c_x h_x => make_call c_x h_x y (fun _ y a => make (h_x a) y)
      | Choose _ x1 x2 k_x =>
        match y with
        | Ret v_y => ChooseRet x1 x2 k_x v_y
        | Call c_y h_y =>
          ChooseCall k_x (make x1 (Call c_y h_y)) (make x2 (Call c_y h_y))
        | Choose _ y1 y2 k_y =>
          ChooseChoose k_x k_y
            (make x1 y1) (make x1 y2) (make x2 y1) (make x2 y2)
        end
      end.

    Fixpoint join {E A B} {x y} (xy : t x y) : Choose.t E (A * B) :=
      match xy with
      | RetRet v_x v_y => Ret (v_x, v_y)
      | RetCall v_x c_y h_y => bind (Call c_y h_y) (fun y => Ret (v_x, y))
      | RetChoose _ v_x y1 y2 k_y =>
        bind (Choose y1 y2 k_y) (fun y => Ret (v_x, y))
      | CallRet c_x h_x v_y => bind (Call c_x h_x) (fun x => Ret (x, v_y))
      | CallCall c_x _ c_y _ m_x m_y =>
        Choose (Call c_x (fun a => join (m_x a)))
          (Call c_y (fun a => join (m_y a)))
          (fun x => Ret x)
      | CallChoose _ _ _ _ _ k_y m_y1 m_y2 =>
        Choose (join m_y1) (join m_y2) (fun xy =>
          let (x, y) := xy in
          bind (k_y y) (fun y => Ret (x, y)))
      | ChooseRet _ x1 x2 k_x v_y =>
        bind (Choose x1 x2 k_x) (fun x => Ret (x, v_y))
      | ChooseCall _ _ _ k_x _ _ m_x1 m_x2 =>
        Choose (join m_x1) (join m_x2) (fun xy =>
          let (x, y) := xy in
          bind (k_x x) (fun x => Ret (x, y)))
      | ChooseChoose _ _ _ _ _ _ k_x k_y m_11 m_12 m_21 m_22 =>
        Choose
          (Choose (join m_11) (join m_12) Ret)
          (Choose (join m_21) (join m_22) Ret)
          (fun xy =>
            let (x, y) := xy in
            bind (k_x x) (fun x =>
            bind (k_y y) (fun y =>
            Ret (x, y))))
      end.
  End Mix.
End Choose.
