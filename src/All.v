Require Import Coq.Lists.List.
Require Import Io.All.

Import ListNotations.
Import C.Notations.

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

  Fixpoint compile {E A B} (x : C.t E A) : (A -> t E B) -> t E B :=
    match x with
    | C.Ret _ v => fun k => k v
    | C.Call c => fun k => Call c k
    | C.Let _ _ x f => fun k => compile x (fun x => compile (f x) k)
    | C.Join _ _ x y => fun k =>
      let xy := Mix.make (compile x Ret) (compile y Ret) in
      bind (Mix.join xy) k
    | C.First _ _ x y => fun k =>
      let x := compile x (fun x => Ret (inl x)) in
      let y := compile y (fun y => Ret (inr y)) in
      Choose x y k
    end.

  (*Fixpoint is_not_stuck {E S A} (m : Model.t E S) (x : Choose.t E A) (s : S)
    : bool :=
    match x with
    | Ret _ => true
    | Call c _ => Model.condition m c s
    | Choose x1 x2 => orb (is_not_stuck m x1 s) (is_not_stuck m x2 s)
    end.

  Fixpoint aux {E S} (m : Model.t E S) (post : S -> bool) (x : Choose.t E)
    (s : S) : bool :=
    match x with
    | Ret => post s
    | Call c h =>
      if Model.condition m c s then
        let a := Model.answer m c s in
        let s := Model.state m c s in
        andb (is_not_stuck m (h a) s) (aux m post (h a) s)
      else
        true
    | Choose x1 x2 => andb (aux m post x1 s) (aux m post x2 s)
    end.

  Definition check {E S} (m : Model.t E S) (post : S -> bool) (x : Choose.t E)
    (s : S) : bool :=
    andb (is_not_stuck m x s) (aux m post x s).*)
End Choose.

Module Lock.
  Definition S := bool.

  Module Command.
    Inductive t :=
    | Lock
    | Unlock.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t (fun _ => unit).

  Definition lock : C.t E unit :=
    call E Command.Lock.

  Definition unlock : C.t E unit :=
    call E Command.Unlock.

  Definition condition (c : Effect.command E) (s : S) : bool :=
    match (c, s) with
    | (Command.Lock, false) | (Command.Unlock, true) => true
    | (Command.Lock, true) | (Command.Unlock, false) => false
    end.

  Definition answer (c : Effect.command E) (s : S) : Effect.answer E c :=
    tt.

  Definition state (c : Effect.command E) (s : S) : S :=
    match c with
    | Command.Lock => true
    | Command.Unlock => false
    end.

  Definition m : Model.t E S :=
    Model.New condition answer state.

  Fixpoint ex1 (n : nat) : C.t E unit :=
    match n with
    | O => ret tt
    | Datatypes.S n =>
      let! _ : unit * unit := join (ex1 n) (do! lock in unlock) in
      ret tt
    end.

  Compute ex1 2.
  Compute Choose.compile (ex1 2) Choose.Ret.
End Lock.
