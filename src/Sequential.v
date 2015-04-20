(** * Evaluation of concurrent computations in a sequential monad. *)
Require Import Io.All.

(** * Sequential computations. *)
Module S.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall {A : Type} (x : A), t E A
  | Call : forall (c : Effect.command E), t E (Effect.answer E c)
  | Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B.
  Arguments Ret {E A} _.
  Arguments Call {E} _.
  Arguments Let {E A B} _ _.

  (** A nicer notation for `Ret`. *)
  Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
    Ret x.

  (** A nicer notation for `Call`. *)
  Definition call (E : Effect.t) (c : Effect.command E)
    : t E (Effect.answer E c) :=
    Call (E := E) c.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Let`. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (Let X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (Let X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the unit answer. *)
    Notation "'do!' X 'in' Y" :=
      (Let X (fun (_ : unit) => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End S.

Module Eval.
  Import S.Notations.

  Module Choose.
    Inductive t (E : Effect.t) : Type :=
    | Choose : t E
    | Call : Effect.command E -> t E.
    Arguments Choose {E}.
    Arguments Call {E} _.

    Definition answer {E : Effect.t} (c : t E) : Type :=
      match c with
      | Choose => bool
      | Call c => Effect.answer E c
      end.

    Definition E (E : Effect.t) : Effect.t :=
      Effect.New (t E) answer.

    Definition choose {E} : S.t (Choose.E E) bool :=
      S.call (Choose.E E) Choose.

    Definition call {E} (c : Effect.command E)
      : S.t (Choose.E E) (Effect.answer E c) :=
      S.call (Choose.E E) (Call c).
  End Choose.

  Fixpoint eval {E A} (x : C.t E A) : S.t (Choose.E E) A :=
    match x with
    | C.Ret _ v => S.ret v
    | C.Call c => Choose.call c
    | C.Let _ _ x f =>
      let! v_x := eval x in
      eval (f v_x)
    | C.Choose _ x1 x2 =>
      let! choice := Choose.choose in
      if choice then
        eval x1
      else
        eval x2
    | C.Join _ _ x y =>
      let! x := eval x in
      let! y := eval y in
      match (x, y) with
      | (inl v_x, inl v_y) => S.ret (inl (v_x, v_y))
      | (inr c_x, inl _) => S.ret (inr c_x)
      | (inl _, inr c_y) => S.ret (inr c_y)
      | (inr c_x, inr c_y) =>
        let! choice := Choose.choose in
        if choice then
          S.ret (inr c_x)
        else
          S.ret (inr c_y)
      end
    end.

  Fixpoint eval {E A} (x : C.t E A) : S.t Choose.E (A + Effect.command E) :=
    match x with
    | C.Ret _ v => S.ret (inl v)
    | C.Call c => S.ret (inr c)
    | C.Let _ _ x f =>
      let! x := eval x in
      match x with
      | inl v => eval (f v)
      | inr c => S.ret (inr c)
      end
    | C.Choose _ x1 x2 =>
      let! choice := Choose.choose in
      if choice then
        eval x1
      else
        eval x2
    | C.Join _ _ x y =>
      let! x := eval x in
      let! y := eval y in
      match (x, y) with
      | (inl v_x, inl v_y) => S.ret (inl (v_x, v_y))
      | (inr c_x, inl _) => S.ret (inr c_x)
      | (inl _, inr c_y) => S.ret (inr c_y)
      | (inr c_x, inr c_y) =>
        let! choice := Choose.choose in
        if choice then
          S.ret (inr c_x)
        else
          S.ret (inr c_y)
      end
    end.

  Fixpoint value {E A} (x : C.t E A) : S.t Choose.E A :=
    match x with
    | C.Ret _ v => S.ret v
    | C.Call _ => Choose.abort
    | C.Let _ _ x f =>
      let! x := value x in
      value (f x)
    | C.Choose _ x1 x2 =>
      let! choice := Choose.choose in
      if choice then
        value x1
      else
        value x2
    | C.Join _ _ x y =>
      let! x := value x in
      let! y := value y in
      S.ret (x, y)
    end.

  Fixpoint eval {E A} (x : C.t E A) : S.t Choose.E (Effect.command E) :=
    match x with
    | C.Ret _ _ => Choose.abort
    | C.Call c => S.ret c
    | C.Let _ _ x f =>
    | _ => Choose.abort
    end.
End Eval.
