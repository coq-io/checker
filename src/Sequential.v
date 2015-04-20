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
    Inductive t : Set :=
    | Abort
    | Choose.

    Definition answer (c : t) : Type :=
      match c with
      | Abort => Empty_set
      | Choose => bool 
      end.

    Definition E : Effect.t :=
      Effect.New t answer.

    Definition abort {A : Type} : S.t E A :=
      let! x := S.call E Abort in
      match x with end.

    Definition choose : S.t E bool :=
      S.call E Choose.
  End Choose.

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
    (* | C.Let _ _ x f => *)
    | _ => Choose.abort
    end.
End Eval.
