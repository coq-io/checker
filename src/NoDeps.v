Require Import Io.All.

Definition E (X Y : Type) : Effect.t :=
  Effect.New X (fun _ => Y).
