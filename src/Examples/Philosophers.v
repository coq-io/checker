(** * The dinning of philosphers. *)
Require Import Coq.Arith.EqNat.
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
  Inductive t : Set :=
  | Take (l r : nat)
  | Release (l r : nat).
End Command.

Definition answer (c : Command.t) : Type :=
  unit.

Definition E : Effect.t :=
  Effect.New Command.t answer.

Definition take (l r : nat) : C.t E unit :=
  call E (Command.Take l r).

Definition release (l r : nat) : C.t E unit :=
  call E (Command.Release l r).

Module S.
  Definition t := list bool.

  Fixpoint init (n : nat) : t :=
    List.repeat false n.
End S.

Module List.
  Fixpoint set {A : Type} (l : list A) (n : nat) (a : A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      match n with
      | O => a :: l
      | S n => x :: set l n a
      end
    end.
End List.

Definition model : Model.t E S.t :=
  fun c s =>
    match c with
    | Command.Take l r =>
      let l_b := List.nth l s false in
      let r_b := List.nth r s false in
      if orb l_b r_b then
        None
      else
        Some (tt, List.set (List.set s r true) l true)
    | Command.Release l r =>
      let l_b := List.nth l s false in
      let r_b := List.nth r s false in
      if andb l_b r_b then
        Some (tt, List.set (List.set s r false) l false)
      else
        None
    end.

Fixpoint iter_seq (l : list (C.t E unit)) : C.t E unit :=
  match l with
  | [] => ret tt
  | x :: l => do! x in iter_seq l
  end.

Fixpoint iter_par (l : list (C.t E unit)) : C.t E unit :=
  match l with
  | [] => ret tt
  | x :: l =>
    let! _ : unit * unit := join x (iter_par l) in
    ret tt
  end.

Module Forks.
  Definition init (n : nat) : list (nat * nat) :=
    List.seq 0 n |> List.map (fun p =>
      (p, if beq_nat (p + 1) n then 0 else p + 1)).

  Definition init_ok : init 3 = [(0, 1); (1, 2); (2, 0)] :=
    eq_refl.
End Forks.

Definition philospher (l_r : nat * nat) : C.t E unit :=
  let (l, r) := l_r in
  do! take l r in
  release l r.

Definition diner_seq (n : nat) : C.t E unit :=
  iter_seq @@ List.map philospher @@ Forks.init n.

Definition diner_par (n : nat) : C.t E unit :=
  iter_par @@ List.map philospher @@ Forks.init n.

Lemma diner_seq_ok :
  let n := 6 in
  C.DeadLockFree.t model (S.init n) (diner_seq n).
  now apply Decide.C.dead_lock_free_ok.
Qed.

Lemma diner_par_ok :
  let n := 3 in
  C.DeadLockFree.t model (S.init n) (diner_par n).
  now apply Decide.C.dead_lock_free_ok.
Qed.

Time Compute
  let n := 4 in
  Decide.dead_lock_free model (S.init n) (Compile.to_choose @@ diner_par n).

Definition eval_diner_par (argv : list LString.t) : C.t System.effect unit :=
  let n := 7 in
  if Decide.dead_lock_free
    model (S.init n) (Compile.to_choose @@ diner_par n) then
    System.log (LString.s "OK")
  else
    System.log (LString.s "error").

Definition main := Extraction.launch eval_diner_par.
Extraction "extraction/main" main.
