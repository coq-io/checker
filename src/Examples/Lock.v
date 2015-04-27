(** * One global lock. *)
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import DeadLockFree.
Require Decide.
Require Model.

Import ListNotations.
Import C.Notations.

Module Lock.
  Module Command.
    Inductive t : Set :=
    | Lock | Unlock.
  End Command.

  Definition answer (c : Command.t) : Type :=
    unit.

  Definition E : Effect.t :=
    Effect.New Command.t answer.

  Definition lock : C.t E unit :=
    call E Command.Lock.

  Definition unlock : C.t E unit :=
    call E Command.Unlock.

  Definition S := bool.
  
  Module Model.
    Module Pre.
      Inductive t : Effect.command E -> S -> Prop :=
      | Lock : t Command.Lock false
      | Unlock : t Command.Unlock true.
    End Pre.

    Definition answer c s (H : Pre.t c s) : Effect.answer E c :=
      tt.

    Definition state c s (H : Pre.t c s) : S :=
      negb s.

    Lemma stable_answer c s (H1 H2 : Pre.t c s) : answer c s H1 = answer c s H2.
      reflexivity.
    Qed.

    Lemma stable_state c s (H1 H2 : Pre.t c s) : state c s H1 = state c s H2.
      reflexivity.
    Qed.
  End Model.

  Definition m : Model.t E S :=
    Model.New Model.Pre.t Model.answer Model.state
      Model.stable_answer Model.stable_state.

  Definition dec : Model.Dec.t m.
    intros c s.
    destruct c.
    - destruct s.
      + right.
        intro H.
        inversion H.
      + left.
        apply Model.Pre.Lock.
    - destruct s.
      + left.
        apply Model.Pre.Unlock.
      + right.
        intro H.
        inversion H.
  Defined.
End Lock.

Definition ex1 : C.t Lock.E nat :=
  do! Lock.lock in
  do! Lock.unlock in
  ret 12.

Lemma ex1_ok : C.DeadLockFree.t Lock.m false ex1.
  now apply (Decide.C.dead_lock_free_ok Lock.dec).
Qed.

Fixpoint ex2 (l : list nat) : C.t Lock.E nat :=
  match l with
  | [] => ret 0
  | n :: l =>
    let! n :=
      do! Lock.lock in
      do! Lock.unlock in
      ret n in
    let! s := ex2 l in
    ret (n + s)
  end.

Lemma ex2_ok : C.DeadLockFree.t Lock.m false (ex2 [1; 2; 3; 4; 5]).
  now apply (Decide.C.dead_lock_free_ok Lock.dec).
Qed.

Fixpoint ex3 (l : list nat) : C.t Lock.E nat :=
  match l with
  | [] => ret 0
  | n :: l =>
    let! s_n :=
      join (ex3 l) (
        do! Lock.lock in
        do! Lock.unlock in
        ret n) in
    let (s, n) := s_n in
    ret (n + s)
  end.

Lemma ex3_ok : C.DeadLockFree.t Lock.m false (ex3 [1; 2; 3]).
  now apply (Decide.C.dead_lock_free_ok Lock.dec).
Qed.

Definition good_lock : C.t Lock.E unit :=
  choose Lock.lock Lock.unlock.

Fixpoint ex4 (l : list nat) : C.t Lock.E nat :=
  match l with
  | [] => ret 0
  | n :: l =>
    let! s_n :=
      join (ex4 l) (
        do! Lock.lock in
        do! good_lock in
        ret n) in
    let (s, n) := s_n in
    ret (n + s)
  end.

Lemma ex4_ok : C.DeadLockFree.t Lock.m false (ex4 [1; 2; 3]).
  now apply (Decide.C.dead_lock_free_ok Lock.dec).
Qed.

Time Compute Decide.dead_lock_free Lock.dec false
  (Compile.to_choose (ex4 [1; 2; 3; 4; 5])).
