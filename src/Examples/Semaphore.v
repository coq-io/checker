(** * One global semaphore. *)
Require Coq.Vectors.Fin.
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
  Inductive t : Set :=
  | Incr | Decr.
End Command.

Definition answer (c : Command.t) : Type :=
  unit.

Definition E : Effect.t :=
  Effect.New Command.t answer.

Definition incr : C.t E unit :=
  call E Command.Incr.

Definition decr : C.t E unit :=
  call E Command.Decr.

Definition S (n : nat) := Fin.t n.

Definition m (n : nat) : Model.t E (S n) :=
  fun c s =>
    match c with
    | Command.Incr =>
      let (s, _) := Fin.to_nat s in
      match Fin.of_nat (Datatypes.S s) n with
      | inleft s => Some (tt, s)
      | inright _ => None
      end
    | Command.Decr =>
      let (s, _) := Fin.to_nat s in
      match s with
      | O => None
      | Datatypes.S s =>
        match Fin.of_nat s n with
        | inleft s => Some (tt, s)
        | inright _ => None
        end
      end
    end.
