(** * One global message box. *)
Require Import Coq.Lists.List.
Require Import Io.All.
Require Import DeadLockFree.
Require Decide.
Require Model.

Import ListNotations.
Import C.Notations.

Module Lock.
  Module Command.
    Inductive t (A : Type) : Type :=
    | Send (x : A)
    | Receive.
  End Command.

  Definition answer {A : Type} (c : Command.t A) : Type :=
    match c with
    | Command.Send x => unit
    | Command.Receive => A
    end.

  Definition E (A : Type) : Effect.t :=
    Effect.New (Command.t A) answer.

  Definition send {A : Type} (x : A) : C.t (E A) unit :=
    call (E A) (Command.Send A x).

  Definition receive {A : Type} : C.t (E A) A :=
    call (E A) (Command.Receive A).

  Definition S (A : Type) := option A.

  Definition m (A : Type) : Model.t (E A) (S A) :=
    fun c s =>
      match c with
      | Command.Send x =>
        match s with
        | None => Some (tt, Some x)
        | Some _ => None
        end
      | Command.Receive =>
        match s with
        | Some x => Some (x, None)
        | None => None
        end
      end.
End Lock.
