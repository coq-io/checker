(** * The main Alcool example. *)
Require Import Coq.Arith.EqNat.
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
  | WriteA (n : nat) | CheckA (n : nat)
  | ReadZ | WriteZ (n : nat)
  | CheckE (n : nat)
  | Lock | Unlock
  | SendX (n : nat) | ReceiveX
  | SendY (n : nat) | ReceiveY.
End Command.

Definition answer (c : Command.t) : Type :=
  match c with
  | Command.WriteA _ => unit
  | Command.CheckA _ => unit
  | Command.ReadZ => nat
  | Command.WriteZ _ => unit
  | Command.CheckE _ => unit
  | Command.Lock => unit
  | Command.Unlock => unit
  | Command.SendX _ => unit
  | Command.ReceiveX => nat
  | Command.SendY _ => unit
  | Command.ReceiveY => nat
  end.

Definition E : Effect.t :=
  Effect.New Command.t answer.

Definition write_a (n : nat) : C.t E unit :=
  call E (Command.WriteA n).

Definition check_a (n : nat) : C.t E unit :=
  call E (Command.CheckA n).

Definition read_z : C.t E nat :=
  call E Command.ReadZ.

Definition write_z (n : nat) : C.t E unit :=
  call E (Command.WriteZ n).

Definition check_e (n : nat) : C.t E unit :=
  call E (Command.CheckE n).

Definition lock : C.t E unit :=
  call E Command.Lock.

Definition unlock : C.t E unit :=
  call E Command.Unlock.

Definition send_x (n : nat) : C.t E unit :=
  call E (Command.SendX n).

Definition receive_x : C.t E nat :=
  call E Command.ReceiveX.

Definition send_y (n : nat) : C.t E unit :=
  call E (Command.SendY n).

Definition receive_y : C.t E nat :=
  call E Command.ReceiveY.

Module S.
  Record t : Set := New {
    a : nat;
    z : nat;
    e : nat;
    l : bool;
    x : option nat;
    y : option nat }.
End S.

Definition m : Model.t E S.t :=
  fun c s =>
    let (a, z, e, l, x, y) := s in
    match c return option (Effect.answer E c * S.t) with
    | Command.WriteA n => Some (tt, S.New n z e l x y)
    | Command.CheckA n => if beq_nat a n then Some (tt, s) else None
    | Command.ReadZ => Some (z, s)
    | Command.WriteZ n => Some (tt, S.New a n e l x y)
    | Command.CheckE n => if beq_nat e n then Some (tt, s) else None
    | Command.Lock => if l then None else Some (tt, S.New a z e true x y)
    | Command.Unlock => if l then Some (tt, S.New a z e false x y) else None
    | Command.SendX n =>
      match x with
      | None => Some (tt, S.New a z e l (Some n) y)
      | Some _ => None
      end
    | Command.ReceiveX =>
      match x with
      | Some n => Some (n, S.New a z e l None y)
      | None => None
      end
    | Command.SendY n =>
      match y with
      | None => Some (tt, S.New a z e l x (Some n))
      | Some _ => None
      end
    | Command.ReceiveY =>
      match x with
      | Some n => Some (n, S.New a z e l x None)
      | None => None
      end
    end.
