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
  Inductive t : Type :=
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

Definition model (n : nat) : Model.t E (S n) :=
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

Fixpoint iter_sem (l : list (C.t E unit)) : C.t E unit :=
  match l with
  | [] => ret tt
  | x :: l =>
    let! _ : unit * unit :=
      join (iter_sem l) (
        do! incr in
        do! x in
        decr) in
    ret tt
  end.

Fixpoint map_sem {A B} (f : A -> C.t E B) (l : list A) : C.t E (list B) :=
  match l with
  | [] => ret []
  | x :: l =>
    let! l_y : list B * B :=
      join (map_sem f l) (
        do! incr in
        let! y := f x in
        do! decr in
        ret y) in
    let (l, y) := l_y in
    ret (y :: l)
  end.

Definition ex1 (n : nat) : C.t E (list nat) :=
  map_sem (fun k => ret (k + 1)) (List.seq 0 n).

Lemma ex1_ok : C.DeadLockFree.t (model 3) Fin.F1 (ex1 3).
  now apply Decide.C.dead_lock_free_ok.
Qed.
