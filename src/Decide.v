Require Import Coq.Bool.Bool.
Require Import Io.All.
Require Bisimulation.Equiv.
Require Choose.
Require Import DeadLockFree.
Require Model.
Require NoDeps.
Require Import Semantics.

Fixpoint not_stuck {E S A} (m : Model.t E S) (s : S) (x : Choose.t E A)
  : bool :=
  match x with
  | Choose.Ret _ => true
  | Choose.Call c _ =>
    match m c s with
    | Some _ => true
    | None => false
    end
  | Choose.Choose x1 x2 => orb (not_stuck m s x1) (not_stuck m s x2)
  end.

Fixpoint explore {E S A} (m : Model.t E S) (s : S) (x : Choose.t E A) : bool :=
  match x with
  | Choose.Ret _ => true
  | Choose.Call c h =>
    match m c s with
    | Some (a, s') => andb (not_stuck m s' (h a)) (explore m s' (h a))
    | None => true
    end
  | Choose.Choose x1 x2 => andb (explore m s x1) (explore m s x2)
  end.

Definition dead_lock_free {E S A} (m : Model.t E S) (s : S) (x : Choose.t E A)
  : bool :=
  andb (not_stuck m s x) (explore m s x).

Module Choose.
  Fixpoint not_stuck_ok {E S A} {m : Model.t E S} {s : S} {x : Choose.t E A}
    (H : not_stuck m s x = true)
    : (exists p, exists v, Choose.Last.Eval.t p x v) \/
      (exists c, exists x', exists s', Choose.Step.t m c s x x' s').
    destruct x as [v | c h | x1 x2]; simpl in H.
    - left.
      exists Choose.Path.Done, v.
      apply Choose.Last.Eval.Ret.
    - right.
      case_eq (m c s).
      + intros p H_m; destruct p as [a s'].
        exists c, (h a), s'.
        apply (Choose.Step.New _ _ _ _ _ Choose.Path.Done a s').
        * exact H_m.
        * apply Choose.Eval.Call.
      + intro H_m.
        rewrite H_m in H.
        congruence.
    - destruct (orb_prop _ _ H) as [H_not_stuck | H_not_stuck].
      + destruct (not_stuck_ok _ _ _ _ _ _ H_not_stuck) as
        [[p [v H_last]] | [c [x' [s' H_step]]]].
        * left.
          eexists; eexists.
          apply Choose.Last.Eval.ChooseLeft.
          exact H_last.
        * right.
          exists c, x', s'.
          destruct H_step.
          eapply Choose.Step.New; [exact H0 |].
          apply Choose.Eval.ChooseLeft.
          exact H1.
      + destruct (not_stuck_ok _ _ _ _ _ _ H_not_stuck) as
        [[p [v H_last]] | [c [x' [s' H_step]]]].
        * left.
          eexists; eexists.
          apply Choose.Last.Eval.ChooseRight.
          exact H_last.
        * right.
          exists c, x', s'.
          destruct H_step.
          eapply Choose.Step.New; [exact H0 |].
          apply Choose.Eval.ChooseRight.
          exact H1.
  Defined.

  Fixpoint dead_lock_free_ok_no_deps {X Y S A} {m : Model.t (NoDeps.E X Y) S}
    {s : S} {x : Choose.t (NoDeps.E X Y) A} (H : dead_lock_free m s x = true)
    : Choose.DeadLockFree.t m s x.
    destruct (proj1 (andb_true_iff _ _) H) as [H_not_stuck H_aux].
    apply Choose.DeadLockFree.New.
    - destruct (not_stuck_ok H_not_stuck) as [[p [v H_v]] | [c [x' [s' H_x]]]].
      + left.
        now exists p, v.
      + right.
        now exists c, x', s'.
    - clear H H_not_stuck.
      induction x; intros c' x' s' H_x; simpl in H_aux.
      + inversion_clear H_x.
        inversion H0.
      + inversion_clear H_x.
        inversion H1.
        rewrite <- H4 in *.
        rewrite H0 in H_aux.
        now apply dead_lock_free_ok_no_deps.        
      + inversion_clear H_x.
        destruct (proj1 (andb_true_iff _ _) H_aux) as [H_x1 H_x2].
        inversion_clear H0.
        * apply (IHx1 H_x1 c').
          eapply Choose.Step.New; [exact H |].
          apply H1.
        * apply (IHx2 H_x2 c').
          eapply Choose.Step.New; [exact H |].
          apply H1.
  Qed.

  Definition dead_lock_free_ok {E S A} {m : Model.t E S} {s : S}
    {x : Choose.t E A} (H : dead_lock_free m s x = true)
    : Choose.DeadLockFree.t m s x.
  Admitted.
End Choose.

Module C.
  Definition dead_lock_free_ok {E S A} {m : Model.t E S} {s : S} {x : C.t E A}
    (H : dead_lock_free m s (Compile.to_choose x) = true)
    : C.DeadLockFree.t m s x.
    apply Equiv.to_c.
    now apply Choose.dead_lock_free_ok.
  Qed.
End C.
