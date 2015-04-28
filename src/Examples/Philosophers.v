(** * The dinning of philosphers. *)
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListString.All.
Require Import DeadLockFree.
Require Decide.
Require Model.

Import ListNotations.
Import C.Notations.

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

Module S.
  Definition t (n : nat) := Vector.t bool n.

  Fixpoint init (n : nat) : t n :=
    match n with
    | O => Vector.nil bool
    | Datatypes.S n => Vector.cons bool false n (init n)
    end.
End S.

Definition model (n : nat) : Model.t (E n) (S.t n) :=
  fun c s =>
    match c with
    | Command.Lock id =>
      let b := Vector.nth s id in
      if b then
        None
      else
        Some (tt, Vector.replace s id true)
    | Command.Unlock id =>
      let b := Vector.nth s id in
      if b then
        Some (tt, Vector.replace s id false)
      else
        None
    end.

Fixpoint iter_seq {n : nat} (l : list (C.t (E n) unit)) : C.t (E n) unit :=
  match l with
  | [] => ret tt
  | x :: l => do! x in iter_seq l
  end.

Fixpoint iter_par {n : nat} (l : list (C.t (E n) unit)) : C.t (E n) unit :=
  match l with
  | [] => ret tt
  | x :: l =>
    let! _ : unit * unit := join x (iter_par l) in
    ret tt
  end.
