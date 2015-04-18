Require Import Io.All.
Require SmallSteps.

Local Open Scope type.

Module LeftRight.
Inductive t (E : Effect.t) : Type -> Type :=
| Ret : forall A, A -> t E A
| Call : forall c, t E (Effect.answer E c)
| Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B
| Choose : forall (A : Type), t E A -> t E A -> t E A
| JoinLeft : forall (A B : Type), t E A -> t E B -> t E (A * B)
| JoinRight : forall (A B : Type), t E A -> t E B -> t E (A * B).
Arguments Ret {E A} _.
Arguments Call {E} _.
Arguments Let {E A B} _ _.
Arguments Choose {E A} _ _.
Arguments JoinLeft {E A B} _ _.
Arguments JoinRight {E A B} _ _.

Definition join {E A B} (x : t E A) (y : t E B) : t E (A * B) :=
  Choose (JoinLeft x y) (JoinRight x y).

Module LastStep.
  Inductive t {E : Effect.t} : forall {A}, LeftRight.t E A -> A -> Type :=
  | Ret : forall A (v : A),
    t (LeftRight.Ret v) v
  | Let : forall A B (x : LeftRight.t E A) (f : A -> LeftRight.t E B) v_x v_y,
    t x v_x -> t (f v_x) v_y ->
    t (LeftRight.Let x f) v_y
  | ChooseLeft : forall A (x1 x2 : LeftRight.t E A) v,
    t x1 v ->
    t (LeftRight.Choose x1 x2) v
  | ChooseRight : forall A (x1 x2 : LeftRight.t E A) v,
    t x2 v ->
    t (LeftRight.Choose x1 x2) v
  | JoinLeft : forall A B (x : LeftRight.t E A) v_x (y : LeftRight.t E B) v_y,
    t x v_x -> t y v_y ->
    t (LeftRight.JoinLeft x y) (v_x, v_y)
  | JoinRight : forall A B (x : LeftRight.t E A) v_x (y : LeftRight.t E B) v_y,
    t x v_x -> t y v_y ->
    t (LeftRight.JoinRight x y) (v_x, v_y).
End LastStep.

Module Step.
  Inductive t {E : Effect.t}
    : forall {A}, LeftRight.t E A -> LeftRight.t E A -> Type :=
  | Call : forall c a, t (LeftRight.Call c) (LeftRight.Ret a)
  | Let : forall A B (x x' : LeftRight.t E A) (f : A -> LeftRight.t E B),
    t x x' ->
    t (LeftRight.Let x f) (LeftRight.Let x' f)
  | LetDone : forall A B (x : LeftRight.t E A) (v : A) (f : A -> LeftRight.t E B) (y : LeftRight.t E B),
    LastStep.t x v -> t (f v) y ->
    t (LeftRight.Let x f) y
  | ChooseLeft : forall A (x1 x2 x1' : LeftRight.t E A),
    t x1 x1' ->
    t (LeftRight.Choose x1 x2) x1'
  | ChooseRight : forall A (x1 x2 x2' : LeftRight.t E A),
    t x2 x2' ->
    t (LeftRight.Choose x1 x2) x2'
  | JoinLeft : forall A B (x x' : LeftRight.t E A) (y : LeftRight.t E B),
    t x x' ->
    t (LeftRight.JoinLeft x y) (LeftRight.join x' y)
  | JoinRight : forall A B (x : LeftRight.t E A) (y y' : LeftRight.t E B),
    t y y' ->
    t (LeftRight.JoinRight x y) (LeftRight.join x y').
End Step.

Fixpoint compile {E A} (x : C.t E A) : LeftRight.t E A :=
  match x with
  | C.Ret _ v => LeftRight.Ret v
  | C.Call c => LeftRight.Call c
  | C.Let _ _ x f => LeftRight.Let (compile x) (fun x => compile (f x))
  | C.Choose _ x1 x2 => LeftRight.Choose (compile x1) (compile x2)
  | C.Join _ _ x y => LeftRight.join (compile x) (compile y)
  end.

Module Compile.
  Inductive t {E : Effect.t} : forall {A}, C.t E A -> LeftRight.t E A -> Type :=
  | Ret : forall A (v : A), t (C.Ret _ v) (LeftRight.Ret v)
  | Call : forall c, t (C.Call c) (LeftRight.Call c)
  | Let : forall A B (x : C.t E A) (f : A -> C.t E B) c_x c_f,
    t x c_x -> (forall v_x, t (f v_x) (c_f v_x)) ->
    t (C.Let _ _ x f) (LeftRight.Let c_x c_f)
  | Choose : forall A (x1 x2 : C.t E A) c_x1 c_x2,
    t x1 c_x1 -> t x2 c_x2 ->
    t (C.Choose _ x1 x2) (LeftRight.Choose c_x1 c_x2)
  | Join : forall A B (x : C.t E A) (y : C.t E B) c_x c_y,
    t x c_x -> t y c_y ->
    t (C.Join _ _ x y) (LeftRight.join c_x c_y).

  Fixpoint make {E A} (x : C.t E A) : t x (compile x).
    destruct x.
    - apply Ret.
    - apply Call.
    - now apply Let.
    - now apply Choose.
    - now apply Join.
  Defined.
End Compile.

Require Import Coq.Logic.Eqdep.

Module Inverse.
  Fixpoint compile_ret {E A} {x : C.t E A} {v : A} (H : Compile.t x (Ret v))
    : x = C.Ret _ v.
    inversion H.
    rewrite (inj_pair2 _ _ _ _ _ H3) in H2.
    now rewrite (inj_pair2 _ _ _ _ _ H2).
  Qed.

  Fixpoint compile_ret {E A} {x : C.t E A} {v : A} (H : compile x = Ret v)
    : x = C.Ret _ v.
    destruct x; simpl in H.
    - assert (x = v).
      .
      trivial.
    - 
  Qed.

Module Sound.
  (*Lemma gre A P (x y : sig (A := A) P) (H : x = y) : proj1_sig x = proj1_sig y.
    congruence.
  Qed.

  Lemma gre2 A P (x y : sigT (A := A) P) (H : x = y) : projT1 x = projT1 y.
    congruence.
  Qed.*)


Check inj_pair2.
Print Assumptions inj_pairT2.

  (*Lemma gre3 (A : Type) (T : A -> Type) (x : A) (y1 y2 : T x)
    (H : existT T x y1 = existT T x y2) : y1 = y2.
    apply (f_equal (@projT2 A T)).
    assert (projT2 (existT T x y1) = y1).
    simpl.
    f_equal
  Qed.*)

  (*Fixpoint step {E A} {x x' : C.t E A}
    (H_x : SmallSteps.Step.t x x')
    : Step.t (compile x) (compile x').
    destruct H_x; simpl.
    - apply Step.Call.
    - apply Step.Let.
      now apply step.
    - apply Step.LetDone with (v := v).
      inversion H_eq.
      exists (Ret a).
      rewrite <- (inj_pair2 _ _ _ (Call c) c_x H3).
      split.
      + apply Step.Call.
      + apply Compile.Ret.
    - *)

  Fixpoint step {E A} {x x' : C.t E A}
    (H_x : Step.t (compile x) (compile x'))
    : SmallSteps.Step.t x x'.
    destruct x; simpl in H_x.
    - inversion H_x.
    - inversion H_x.
      rewrite <- (inj_pair2 _ _ _ (Ret a) (compile x') H3) in H_x.
      destruct H_x.
  Defined.

  Fixpoint step {E A} {x : C.t E A} {c_x c_x' : t E A}
    (H_eq : Compile.t x c_x) (H_x : Step.t c_x c_x')
    : {x' : C.t E A & SmallSteps.Step.t x x' * Compile.t x' c_x'}.
    destruct H_x.
    - inversion H_eq.
      exists (C.Ret _ a).
      rewrite H4 in H2.
      rewrite <- (inj_pair2 _ _ _ (C.Call c) x H2).
      split; constructor.
    - 
  Defined.

  Fixpoint step {E A} {x x' : C.t E A} {c_x : t E A}
    (H_eq : Compile.t x c_x) (H_x : SmallSteps.Step.t x x')
    : {c_x' : t E A & Step.t c_x c_x' * Compile.t x' c_x'}.
    destruct H_x.
    - inversion H_eq.
      exists (Ret a).
      rewrite <- (inj_pair2 _ _ _ (Call c) c_x H3).
      split.
      + apply Step.Call.
      + apply Compile.Ret.
    - 
      assert (Call c = c_x).
      Check gre2 _ _ _ _ H3.
      Compute projT1 (existT (fun x : Type => t E x) (answer E c) (Call c)).
      apply (f_equal (@projT1 _ _) H3).
      destruct H_eq.
      + 
      inversion_clear H_eq.
      
    destruct H_eq.
    - inversion H_x.
    - eexists.
      split.
      + apply Step.Call.
      + 
        destruct H_x.
        destruct x'.
        inversion H_x.
        assert (x' = C.Ret E a).
        congruence.
      inversion_clear H_x.
  Defined.

  Fixpoint last_step {E A} {x : C.t E A} {v : A} c_x
    (H : LastStep.t c_x v) : Compile.t x c_x -> SmallSteps.LastStep.t x v.
    destruct H.
    - intro H_c.
      destruct H_c.
      inversion H_c. apply SmallSteps.LastStep.Ret.
  Defined.
End Sound.
