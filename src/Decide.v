Require Import Io.All.
Require Choose.
Require DeadLockFree.
Require Model.

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

Fixpoint dead_lock_free_ok {E S A} {m : Model.t E S} {dec : Model.Dec.t m}
  {s : S} {x : Choose.t E A} (H : dead_lock_free dec s x = true)
  : DeadLockFree.Choose2.t m s x.
  intros trace s' x' H_trace H_not_stuck.
  inversion H_trace.
  - rewrite <- H0 in H_not_stuck.
    exists 
    inversion_clear H_not_stuck.
    
Qed.

(*Fixpoint not_stuck_ok {E S A} {m : Model.t E S} {dec : Model.Dec.t m} {s : S}
  {x : Choose.t E A} (H : not_stuck dec s x = true)
  : DeadLockFree.NotStuck.t
Qed.*)
