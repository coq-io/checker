(** * The small-steps relation is well-founded. *)
Require Import Io.All.
Require SmallSteps.

Definition t {E A} (x : C.t E A) : Prop :=
  Acc (fun x x' => SmallSteps.Step.t x' x) x.

Lemma ret {E A} (v : A) : t (C.Ret E v).
  apply Acc_intro.
  intros x' H.
  destruct H.
  inversion l.
Qed.

Lemma call {E} (c : Effect.command E) : t (C.Call c).
  apply Acc_intro.
  intros x' H.
  inversion_clear H.
  apply ret.
Qed.

Lemma let_ {E A B} (x : C.t E A) (f : A -> C.t E B) : t (C.Let _ _ x f).
  apply Acc_intro.
  intros x' H.
  
Qed.

Fixpoint well_founded {E A} (x : C.t E A) : t x.
  destruct x.
  - apply ret.
  - apply call.
  - 
Qed.
  
End Accessible.

Lemma step_ret {E A} (v : A) (x' : C.t E A)
  : ~ SmallSteps.Step.t (C.Ret _ v) x'.
  intro H.
  inversion H.
Qed.

(*Fixpoint acc {E A} {P : C.t E A -> Prop} (x : C.t E A)
  (H : forall x', SmallSteps.Step.t x x' -> P x') {struct x}
  : P x :=
  match x with
  | C.Ret _ v => H step_ret v
  end.
Qed.
  : Acc (fun x x' => SmallSteps.Step.t x' x) x.*)

Fixpoint acc {E : Effect.t} {A : Type} (x : C.t E A) {struct x}
  : Acc (fun x x' => SmallSteps.Step.t x' x) x :=
  Acc_intro (
    match x return C.t E A -> _ -> Acc (fun x x' => SmallSteps.Step.t x' x) x with
    | C.Ret _ v => fun x' H => match step_ret v x' H with end
    end).
  apply Acc_intro.
  intros x' H.
  destruct x.
  - inversion H.
  - inversion_clear H.
    apply acc.
  - inversion_clear H.
    + apply acc.
    + apply acc.
  - inversion_clear H.
    + apply acc.
    + apply acc.
  - inversion_clear H.
    + apply acc.
    + apply acc.
Qed.
