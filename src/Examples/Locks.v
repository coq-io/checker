(** * A finite number of global locks. *)
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import DeadLockFree.
Require Decide.
Require Model.

Import ListNotations.
Import C.Notations.

Module Locks.
  Module Command.
    Inductive t (n : nat) : Set :=
    | Lock (id : Fin.t n)
    | Unlock (id : Fin.t n).
  End Command.

  Definition answer {n : nat} (c : Command.t n) : Type :=
    unit.

  Definition E (n : nat) : Effect.t :=
    Effect.New (Command.t n) answer.

  Definition lock {n : nat} (id : Fin.t n) : C.t (E n) unit :=
    call (E n) (Command.Lock n id).

  Definition unlock {n : nat} (id : Fin.t n) : C.t (E n) unit :=
    call (E n) (Command.Unlock n id).

  Definition S (n : nat) := Vector.t bool n.

  Definition m (n : nat) : Model.t (E n) (S n) :=
    fun c s =>
      match c with
      | Command.Lock id =>
        let b := Vector.nth s id in
        if b then
          None
        else
          Some (tt, Vector.replace s id false)
      | Command.Unlock id =>
        let b := Vector.nth s id in
        if b then
          Some (tt, Vector.replace s id true)
        else
          None
      end.
End Locks.
