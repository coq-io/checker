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
  Inductive t (A B : Type) : Type :=
  | Incr | Decr
  | Action (x : A).
End Command.

Definition answer {A B : Type} (c : Command.t A B) : Type :=
  match c with
  | Command.Incr | Command.Decr => unit
  | Command.Action _ => B
  end.

Definition E (A B : Type) : Effect.t :=
  Effect.New (Command.t A B) answer.

Definition incr {A B : Type} : C.t (E A B) unit :=
  call (E A B) (Command.Incr A B).

Definition decr {A B : Type} : C.t (E A B) unit :=
  call (E A B) (Command.Decr A B).

Definition action {A B : Type} (x : A) : C.t (E A B) B :=
  call (E A B) (Command.Action A B x).

Definition S (n : nat) := Fin.t n.

Definition m {A B : Type} (n : nat) (f : A -> B) : Model.t (E A B) (S n) :=
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
    | Command.Action x => Some (f x, s)
    end.

Fixpoint fold_par {A B : Type} (f : B -> B -> B) (l : list A) (r : B)
  : C.t (E A B) B :=
  match l with
  | [] => ret r
  | a :: l =>
    let! b_r := join (fold_par f l r) (
      do! incr in
      let! b := action a in
      do! decr in
      ret b) in
    let (b, r) := b_r in
    ret (f b r)
  end.

Definition ex1 (n : nat) : C.t (E nat nat) nat :=
  fold_par plus (List.seq 0 n) 0.

(* Time Compute Decide.dead_lock_free (m 3 id) Fin.F1 (Compile.to_choose (ex1 4)). *)

Definition eval_ex1 (argv : list LString.t) : C.t System.effect unit :=
  if Decide.dead_lock_free (m 3 id) Fin.F1 (Compile.to_choose (ex1 5)) then
    System.log (LString.s "OK")
  else
    System.log (LString.s "error").

Definition main := Extraction.run eval_ex1.
Extraction "extraction/main" main.

Lemma ex1_ok : C.DeadLockFree.t (m 12 id) Fin.F1 (ex1 2).
  now apply Decide.C.dead_lock_free_ok.
Qed.
