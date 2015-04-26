Require Import Coq.Bool.Bool.
Require Import Io.All.
Require Choose.
Require DeadLockFree.
Require Model.
Require NoDeps.
Require Import Semantics.

Fixpoint not_stuck {E S A} {m : Model.t E S} (dec : Model.Dec.t m) (s : S)
  (x : Choose.t E A) : bool :=
  match x with
  | Choose.Ret _ => true
  | Choose.Call c _ => if dec c s then true else false
  | Choose.Choose x1 x2 => orb (not_stuck dec s x1) (not_stuck dec s x2)
  end.

Fixpoint aux {E S A} {m : Model.t E S} (dec : Model.Dec.t m) (s : S)
  (x : Choose.t E A) : bool :=
  match x with
  | Choose.Ret _ => true
  | Choose.Call c h =>
    match dec c s with
    | left H =>
      let s' := Model.state m c s H in
      let x' := h (Model.answer m c s H) in
      andb (not_stuck dec s' x') (aux dec s' x')
    | right _ => true
    end
  | Choose.Choose x1 x2 => andb (aux dec s x1) (aux dec s x2)
  end.

Definition dead_lock_free {E S A} {m : Model.t E S} (dec : Model.Dec.t m)
  (s : S) (x : Choose.t E A) : bool :=
  andb (not_stuck dec s x) (aux dec s x).

Axiom falso : False.

Fixpoint not_stuck_ok {E S A} {m : Model.t E S} {dec : Model.Dec.t m} {s : S}
  {x : Choose.t E A} (H : not_stuck dec s x = true)
  : (exists v, Choose.LastStep.t x v) \/
    (exists c, exists x', exists s', Choose.Step.t m c s x x' s').
  destruct x as [v | c h | x1 x2]; simpl in H.
  - left.
    exists v.
    apply (Choose.LastStep.New _ _ Choose.Path.Done).
    apply Choose.Last.Eval.Ret.
  - right.
    destruct (dec c s) as [H_pre |].
    + exists c, (h (Model.answer m c s H_pre)), (Model.state m c s H_pre).
      apply (Choose.Step.New _ _ _ _ _ Choose.Path.Done).
      apply Choose.Eval.Call.
    + congruence.
  - destruct falso.
Defined.

(*Fixpoint aux_ok {E S A} {m : Model.t E S} {dec : Model.Dec.t m} {s s' : S}
  {x x' : Choose.t E A} (H_aux : aux dec s x = true)
  (H_x : Choose.Step.t m s x x' s') : dead_lock_free dec s' x' = true.
Admitted.*)

Fixpoint dead_lock_free_ok {X Y S A} {m : Model.t (NoDeps.E X Y) S}
  {dec : Model.Dec.t m} {s : S} {x : Choose.t (NoDeps.E X Y) A}
  (H : dead_lock_free dec s x = true) : DeadLockFree.Choose2.t m s x.
  destruct (proj1 (andb_true_iff _ _) H) as [H_not_stuck H_aux].
  destruct (not_stuck_ok H_not_stuck) as [[v H_v] | [c [x' [s' H_x]]]].
  - now apply (DeadLockFree.Choose2.Ret _ _ _ v).
  - apply (DeadLockFree.Choose2.Call _ _ _ _ x' s' H_x).
    clear c x' s' H_x H H_not_stuck.
    induction x; intros c' x' s' H_x; simpl in H_aux.
    + inversion_clear H_x.
      inversion H0.
    + inversion_clear H_x.
      replace c with c' in * by (destruct falso).
      inversion_clear H1.
      destruct (dec c' s) as [H_pre | H_not_pre]; simpl in H_aux.
      * replace H_pre with H0 in H_aux by (destruct falso).
        now apply (dead_lock_free_ok _ _ _ _ _ dec).
      * destruct (H_not_pre H0).
    + inversion_clear H_x.
      destruct (proj1 (andb_true_iff _ _) H_aux) as [H_x1 H_x2].
      inversion_clear H0.
      * apply (IHx1 H_x1 c').
        eapply Choose.Step.New.
        apply H1.
      * apply (IHx2 H_x2 c').
        eapply Choose.Step.New.
        apply H1.
Qed.
