(** * The dinning of philosphers. *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListPlus.All.
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

Module Forks.
  Definition of_nat (p n : nat) : option (Fin.t n) :=
    match Fin.of_nat p n with
    | inleft p => Some p
    | inright _ => None
    end.

  Definition init (n : nat) : list (Fin.t n * Fin.t n) :=
    seq 0 n |>
      List.map (fun p =>
        Option.bind (of_nat p n) (fun l =>
        Option.bind (of_nat (if beq_nat (p + 1) n then 0 else p + 1) n) (fun r =>
        Some (l, r))))
    |> List.remove_nones.

  Definition init_ok : init 3 = [
    (Fin.F1, Fin.FS Fin.F1);
    (Fin.FS Fin.F1, Fin.FS (Fin.FS Fin.F1));
    (Fin.FS (Fin.FS Fin.F1), Fin.F1)] :=
    eq_refl.
End Forks.

Definition philospher {n : nat} (l_r : Fin.t n * Fin.t n) : C.t (E n) unit :=
  let (l, r) := l_r in
  do! take l r in
  release l r.

Definition diner_seq (n : nat) : C.t (E n) unit :=
  iter_seq @@ List.map philospher @@ Forks.init n.

Definition diner_par (n : nat) : C.t (E n) unit :=
  iter_par @@ List.map philospher @@ Forks.init n.

Lemma diner_seq_ok :
  let n := 6 in
  C.DeadLockFree.t (model n) (S.init n) (diner_seq n).
  now apply Decide.C.dead_lock_free_ok.
Qed.

Lemma diner_par_ok :
  let n := 3 in
  C.DeadLockFree.t (model n) (S.init n) (diner_par n).
  now apply Decide.C.dead_lock_free_ok.
Qed.

Time Compute
  let n := 4 in
  Decide.dead_lock_free (model n) (S.init n) (Compile.to_choose @@ diner_par n).

Definition eval_diner_par (argv : list LString.t) : C.t System.effect unit :=
  let n := 5 in
  if Decide.dead_lock_free
    (model n) (S.init n) (Compile.to_choose @@ diner_par n) then
    System.log (LString.s "OK")
  else
    System.log (LString.s "error").

Definition main := Extraction.run eval_diner_par.
Extraction "extraction/main" main.
