(** * One global lock. *)
Require Import Io.All.
Require Model.

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
