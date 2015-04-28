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
  | Take (l r : Fin.t n)
  | Release (l r : Fin.t n).
End Command.

Definition answer {n : nat} (c : Command.t n) : Type :=
  unit.

Definition E (n : nat) : Effect.t :=
  Effect.New (Command.t n) answer.

Definition take {n : nat} (l r : Fin.t n) : C.t (E n) unit :=
  call (E n) (Command.Take n l r).

Definition release {n : nat} (l r : Fin.t n) : C.t (E n) unit :=
  call (E n) (Command.Release n l r).

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
    | Command.Take l r =>
      let l_b := Vector.nth s l in
      let r_b := Vector.nth s r in
      if orb l_b r_b then
        None
      else
        Some (tt, Vector.replace (Vector.replace s r true) l true)
    | Command.Release l r =>
      let l_b := Vector.nth s l in
      let r_b := Vector.nth s r in
      if andb l_b r_b then
        Some (tt, Vector.replace (Vector.replace s r false) l false)
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

Definition philospher {n : nat} (l r : Fin.t n) : C.t (E n) unit :=
  do! take l r in
  release l r.

Definition diner_2 : C.t (E 2) unit :=
  iter_par [
    philospher Fin.F1 (Fin.FS Fin.F1);
    philospher (Fin.FS Fin.F1) Fin.F1].

Lemma diner_2_ok : C.DeadLockFree.t (model 2) (S.init 2) diner_2.
  now apply Decide.C.dead_lock_free_ok.
Qed.

Definition diner_3 : C.t (E 3) unit :=
  iter_par [
    philospher Fin.F1 (Fin.FS Fin.F1);
    philospher (Fin.FS Fin.F1) (Fin.FS (Fin.FS Fin.F1));
    philospher (Fin.FS (Fin.FS Fin.F1)) Fin.F1].

Lemma diner_3_ok : C.DeadLockFree.t (model 3) (S.init 3) diner_3.
  now apply Decide.C.dead_lock_free_ok.
Qed.
