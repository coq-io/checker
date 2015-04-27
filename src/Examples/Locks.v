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

  Fixpoint init (n : nat) : S n :=
    match n with
    | O => Vector.nil bool
    | Datatypes.S n => Vector.cons bool false n (init n)
    end.

  Definition m (n : nat) : Model.t (E n) (S n) :=
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
End Locks.

Definition ex1 : C.t (Locks.E 1) nat :=
  do! Locks.lock Fin.F1 in
  do! Locks.unlock Fin.F1 in
  ret 12.

Lemma ex1_ok : C.DeadLockFree.t (Locks.m 1) (Locks.init 1) ex1.
  now apply Decide.C.dead_lock_free_ok.
Qed.

Fixpoint iter_seq {n : nat} (l : list (C.t (Locks.E n) unit))
  : C.t (Locks.E n) unit :=
  match l with
  | [] => ret tt
  | x :: l => do! x in iter_seq l
  end.

Fixpoint iter_par {n : nat} (l : list (C.t (Locks.E n) unit))
  : C.t (Locks.E n) unit :=
  match l with
  | [] => ret tt
  | x :: l =>
    let! _ : unit * unit := join x (iter_par l) in
    ret tt
  end.

Definition ex2 : C.t (Locks.E 3) unit :=
  let a : Fin.t 3 := Fin.F1 in
  let b : Fin.t 3 := Fin.FS Fin.F1 in
  let c : Fin.t 3 := Fin.FS (Fin.FS Fin.F1) in
  iter_par (List.map iter_seq [
    [Locks.lock a; Locks.lock c; Locks.unlock c; Locks.unlock a];
    [Locks.lock a; Locks.lock c; Locks.unlock c; Locks.unlock a];
    [Locks.lock b; Locks.lock c; Locks.unlock c; Locks.unlock b];
    [Locks.lock b; Locks.lock c; Locks.unlock c; Locks.unlock b]]).

Time Compute Decide.dead_lock_free (Locks.m 3) (Locks.init 3)
  (Compile.to_choose ex2).

Lemma ex2_ok : C.DeadLockFree.t (Locks.m 3) (Locks.init 3) ex2.
  now apply Decide.C.dead_lock_free_ok.
Qed.
