(** * The small-steps relation is well-founded. *)
Require Import Io.All.
Require Import SmallSteps.

Axiom any : forall (A : Type), A.

Inductive t {E : Effect.t} {A : Type} : C.t E A -> Prop :=
| New : forall x, (forall (l : Location.t x) a, t (Location.reduce l a)) -> t x.

(*Fixpoint fixpoint {E} {T : forall {A} {x : C.t E A}, Location.t x -> Type}
  (F : forall {A} {x : C.t E A} (l : Location.t x),
    (forall y:A, R y x -> T y) -> T x) ->
  forall {A} {x : C.t E A} (l : Location.t x), T l.*)

Check fun {E : Effect.t} {T : forall {A}, C.t E A -> Type} =>
  Location.t_rect E (fun _ _ l => forall a, T (Location.reduce l a)).

Fixpoint let_ {E A B} (x : C.t E A) (f : A -> C.t E B)
  (acc_x : t x) (acc_f : forall v, t (f v)) {struct acc_x} : t (C.Let _ _ x f).
  destruct acc_x as [x H].
  apply New.
  intros l.
  refine (
    match l as l' in Location.t x return
      match x with
      | C.Let _ _ _ _ => forall a, t (Location.reduce l' a)
      | _ => unit
      end with
    | Location.Let _ _ _ _ l_x => _
    | Location.LetDone _ _ _ _ _ _ l_f_x => _
    | _ => tt
    end).
  - simpl.
    intro a.
    apply let_.
    + apply H.
    simpl.
  inversion_clear l.
  - apply let_.
Defined.

Fixpoint ww {E A} {x : C.t E A} (l : Location.t x) : t x.
  destruct l.
  - exact (New (C.Call c) (fun (l : Location.t (C.Call c)) =>
      match l in Location.t x
        return (
          match x with
          | C.Call _ => forall a, t (Location.reduce l a)
          | _ => unit
          end) with
      | Location.Call _ => fun a =>
        New (C.Ret E a) (fun l _ => match l with end)
      | _ => tt
      end)).
  - apply New.
    
Qed.

Fixpoint well_founded {E A} (x : C.t E A) : t x :=
  match x with
  | C.Ret _ v => New (C.Ret E v) (fun l _ => match l with end)
  | C.Call c =>
    New (C.Call c) (fun (l : Location.t (C.Call c)) =>
      match l in Location.t x
        return (
          match x with
          | C.Call _ => forall a, t (Location.reduce l a)
          | _ => unit
          end) with
      | Location.Call _ => fun a =>
        New (C.Ret E a) (fun l _ => match l with end)
      | _ => tt
      end)
  | C.Let _ _ x f =>
    New (C.Let _ _ x f) (fun (l : Location.t (C.Let _ _ x f)) =>
      match l in Location.t x
        return (
          match x with
          | C.Let _ _ _ _ => forall a, t (Location.reduce l a)
          | _ => unit
          end) with
      | Location.Let _ _ _ _ l_x => fun a =>
        any _
      | Location.LetDone _ _ _ _ _ _ l_f_x => fun a => any _
      | _ => tt
      end)
  end.

Fixpoint acc {E A} {P : C.t E A -> Prop} (x : C.t E A)
  (H : forall (l : Location.t x) a, P (Location.reduce l a)) {struct x}
  : P x :=
  match x with
  | C.Ret _ v => H step_ret v
  end.
Qed.

Definition t {E A} (x : C.t E A) : Prop :=
  Acc (fun x x' => SmallSteps.Step.t x' x) x.

Definition ret {E A} (v : A) : t (C.Ret E v).
  apply Acc_intro.
  intros x' H.
  destruct H as [l a].
  exact (match l with end).
Qed.

Lemma call {E} (c : Effect.command E) : t (C.Call c).
  apply Acc_intro.
  intros x' H.
  destruct H as [l a].
  destruct l.
  refine (match l with SmallSteps.Location.Call c => ret _ end).
  Show.
  apply ret.
Qed.

Lemma let_ {E A B} (x : C.t E A) (f : A -> C.t E B) : t (C.Let _ _ x f).
  apply Acc_intro.
  intros x' H.
  
Qed.

Fixpoint well_founded {E A} (x : C.t E A) : t x.
  refine (
    match x with
    | C.Ret _ v => _
    | C.Call c => _
    | C.Let _ _ x f => _
    | C.Choose _ x1 x2 => _
    | C.Join _ _ x y => _
    end);
    apply Acc_intro;
    intros x' H;
    destruct H as [l a].
  - exact (match l with end).
  - refine (
    match l with
    | Location.Call c => 
    end)
  Show.
  destruct x.
  - apply ret.
  - apply call.
  - 
Qed.

(*Lemma ret {E A} (v : A) : t (C.Ret E v).
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
Qed.*)
