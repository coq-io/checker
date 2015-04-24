Require Import Io.All.
Require Choose.
Require Compile.
Require Import Semantics.

Module ToChoose.
  Module Last.
    Fixpoint map {E A B} {p_x x v_x} {f : A -> B}
      (H : Choose.Last.Eval.t p_x x v_x)
      : Choose.Last.Eval.t (E := E) p_x (Choose.map x f) (f v_x).
      destruct H; simpl.
      - apply Choose.Last.Eval.Ret.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply map.
      - apply Choose.Last.Eval.ChooseRight.
        now apply map.
    Qed.

    Fixpoint bind {E A B} {p_x x} {v_x : A} {p_f f} {v_f : B}
      (H_x : Choose.Last.Eval.t p_x x v_x)
      (H_f : Choose.Last.Eval.t p_f (f v_x) v_f)
      : Choose.Last.Eval.t (E := E) (Choose.Last.Path.bind p_x p_f)
        (Choose.bind x f) v_f.
      destruct H_x; simpl.
      - exact H_f.
      - apply Choose.Last.Eval.ChooseLeft.
        eapply bind.
        + exact H_x.
        + exact H_f.
      - apply Choose.Last.Eval.ChooseRight.
        eapply bind.
        + exact H_x.
        + exact H_f.
    Qed.

    Fixpoint join_left {E A B} {p_x x} {v_x : A} {p_y y} {v_y : B}
      (H_x : Choose.Last.Eval.t p_x x v_x) (H_y : Choose.Last.Eval.t p_y y v_y)
      : Choose.Last.Eval.t (E := E)
        (Choose.Last.Path.bind p_x p_y) (Choose.join_left x y) (v_x, v_y).
      destruct H_x; unfold Choose.join_left; simpl.
      - now apply map.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply join_left.
      - apply Choose.Last.Eval.ChooseRight.
        now apply join_left.
    Qed.

    Definition join {E A B} {p_x x} {v_x : A} {p_y y} {v_y : B}
      (H_x : Choose.Last.Eval.t p_x x v_x) (H_y : Choose.Last.Eval.t p_y y v_y)
      : Choose.Last.Eval.t (E := E)
        (Choose.Last.Path.join p_x p_y) (Choose.join x y) (v_x, v_y).
      apply Choose.Last.Eval.ChooseLeft.
      destruct H_x; simpl.
      - now apply map.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply join_left.
      - apply Choose.Last.Eval.ChooseRight.
        now apply join_left.
    Qed.

    Fixpoint to_choose {E A} {p : C.Last.Path.t} {x : C.t E A} {v : A}
      (H : C.Last.Eval.t p x v)
      : Choose.Last.Eval.t
        (Compile.Path.Last.to_choose p) (Compile.to_choose x) v.
      destruct H; simpl.
      - apply Choose.Last.Eval.Ret.
      - apply (bind (v_x := v_x)).
        + now apply to_choose.
        + now apply to_choose.
      - apply Choose.Last.Eval.ChooseLeft.
        now apply to_choose.
      - apply Choose.Last.Eval.ChooseRight.
        now apply to_choose.
      - apply join.
        + now apply to_choose.
        + now apply to_choose.
    Qed.
  End Last.

  Fixpoint bind {E c a A B} {p_x : Choose.Path.t} {x x' f}
    (H : Choose.Eval.t (E := E) (A := A) c a p_x x x')
    : Choose.Eval.t (A := B) c a p_x (Choose.bind x f) (Choose.bind x' f).
    destruct H; simpl.
    - apply (Choose.Eval.Call c a).
    - apply Choose.Eval.ChooseLeft.
      now apply bind.
    - apply Choose.Eval.ChooseRight.
      now apply bind.
  Qed.

  Fixpoint bind_done {E c a A B} {p_x x v p_f f y}
    (H_x : Choose.Last.Eval.t (E := E) (A := A) p_x x v)
    (H_f : Choose.Eval.t (E := E) (A := B) c a p_f (f v) y)
    : Choose.Eval.t c a (Choose.Path.bind p_x p_f) (Choose.bind x f) y.
    destruct H_x; simpl.
    - exact H_f.
    - apply Choose.Eval.ChooseLeft.
      now apply bind_done with (v := v).
    - apply Choose.Eval.ChooseRight.
      now apply bind_done with (v := v).
  Qed.

  Fixpoint join_left {E c a A B} {p_x} {x x' : Choose.t E A} {y : Choose.t E B}
    (H : Choose.Eval.t c a p_x x x')
    : Choose.Eval.t c a p_x (Choose.join_left x y) (Choose.join x' y).
    destruct H; simpl.
    - apply (Choose.Eval.Call c a).
    - apply Choose.Eval.ChooseLeft.
      now apply join_left.
    - apply Choose.Eval.ChooseRight.
      now apply join_left.
  Qed.

  Fixpoint join_right {E c a A B} {x : Choose.t E B} {p_y}
    {y y' : Choose.t E A} (H : Choose.Eval.t c a p_y y y')
    : Choose.Eval.t c a p_y (Choose.join_right x y) (Choose.join x y').
    destruct H; simpl.
    - apply (Choose.Eval.Call c a).
    - apply Choose.Eval.ChooseLeft.
      now apply join_right.
    - apply Choose.Eval.ChooseRight.
      now apply join_right.
  Qed.

  Fixpoint to_choose {E c a A} {p : C.Path.t} {x x' : C.t E A}
    (H : C.Eval.t c a p x x')
    : Choose.Eval.t c a
      (Compile.Path.to_choose p) (Compile.to_choose x) (Compile.to_choose x').
    destruct H; simpl.
    - apply Choose.Eval.Call.
    - apply bind.
      now apply to_choose.
    - apply (bind_done (v := v_x)).
      + now apply Last.to_choose.
      + now apply to_choose.
    - apply Choose.Eval.ChooseLeft.
      now apply to_choose.
    - apply Choose.Eval.ChooseRight.
      now apply to_choose.
    - apply Choose.Eval.ChooseLeft.
      apply join_left.
      now apply to_choose.
    - apply Choose.Eval.ChooseRight.
      apply join_right.
      now apply to_choose.
  Qed.
End ToChoose.

Module ToC.
  Module Last.
    Fixpoint map {E A B} {p : Choose.Last.Path.t} {x : Choose.t E A}
      {f : A -> B} {v : B} (H : Choose.Last.Eval.t p (Choose.map x f) v)
      : exists v_x, Choose.Last.Eval.t p x v_x /\ v = f v_x.
      destruct x; simpl in *.
      - exists a.
        inversion_clear H.
        split.
        + apply Choose.Last.Eval.Ret.
        + reflexivity.
      - inversion H.
      - inversion_clear H.
        + destruct (map _ _ _ _ _ _ _ H0).
          destruct H.
          exists x.
          split.
          * now apply Choose.Last.Eval.ChooseLeft.
          * trivial.
        + destruct (map _ _ _ _ _ _ _ H0).
          destruct H.
          exists x.
          split.
          * now apply Choose.Last.Eval.ChooseRight.
          * trivial.
    Qed.

    Fixpoint bind {E A B} {x : Choose.t E A} {f : A -> Choose.t E B} {v_y : B}
      {p : Choose.Last.Path.t} (H : Choose.Last.Eval.t p (Choose.bind x f) v_y)
      : exists v_x, exists p_x, exists p_f,
        Choose.Last.Path.bind p_x p_f = p /\
        Choose.Last.Eval.t p_x x v_x /\
        Choose.Last.Eval.t p_f (f v_x) v_y.
      destruct x; simpl in *.
      - exists a; exists Choose.Last.Path.Ret; exists p.
        split.
        + reflexivity.
        + split.
          * apply Choose.Last.Eval.Ret.
          * trivial.
      - inversion H.
      - inversion_clear H as [| p1 x1' x2' v' H1 | p2 x1' x2' v' H2].
        + destruct (bind _ _ _ _ _ _ _ H1) as [v_x [p_x [p_f [H_p1 [H_x1]]]]].
          exists v_x; exists (Choose.Last.Path.ChooseLeft p_x); exists p_f.
          simpl.
          rewrite H_p1.
          split; trivial.
          split; trivial.
          now apply Choose.Last.Eval.ChooseLeft.
        + destruct (bind _ _ _ _ _ _ _ H2) as [v_x [p_x [p_f [H_p2 [H_x2]]]]].
          exists v_x; exists (Choose.Last.Path.ChooseRight p_x); exists p_f.
          simpl.
          rewrite H_p2.
          split; trivial.
          split; trivial.
          now apply Choose.Last.Eval.ChooseRight.
    Qed.

    Fixpoint choose {E A} {p_x : Choose.Last.Path.t} {x1 x2 : Choose.t E A}
      {v : A} (H : Choose.Last.Eval.t p_x (Choose.Choose x1 x2) v)
      : match p_x with
        | Choose.Last.Path.Ret => False
        | Choose.Last.Path.ChooseLeft p_x => Choose.Last.Eval.t p_x x1 v
        | Choose.Last.Path.ChooseRight p_x => Choose.Last.Eval.t p_x x2 v
        end.
      now inversion H.
    Qed.

    Fixpoint join {E A B} {p : Choose.Last.Path.t} {x : Choose.t E A}
      {y : Choose.t E B} {v} (H : Choose.Last.Eval.t p (Choose.join x y) v)
      : match p with
        | Choose.Last.Path.Ret => False
        | Choose.Last.Path.ChooseLeft p =>
          Choose.Last.Eval.t p (Choose.join_left x y) v
        | Choose.Last.Path.ChooseRight p =>
          Choose.Last.Eval.t p (Choose.join_right x y) v
        end.
      now inversion_clear H.
    Qed.

    Fixpoint join_left {E A B} {p : Choose.Last.Path.t} {x : Choose.t E A}
      {y : Choose.t E B} {v_x : A} {v_y : B}
      (H : Choose.Last.Eval.t p (Choose.join_left x y) (v_x, v_y))
      : exists p_x, exists p_y,
        p = Choose.Last.Path.bind p_x p_y /\
        Choose.Last.Eval.t p_x x v_x /\
        Choose.Last.Eval.t p_y y v_y.
      destruct x; unfold Choose.join_left in *; simpl in *.
      - exists Choose.Last.Path.Ret; exists p.
        split; trivial.
        destruct (map H) as [v'_y [H_y H_eq]].
        replace a with v_x by congruence.
        replace v_y with v'_y by congruence.
        split.
        + apply Choose.Last.Eval.Ret.
        + apply H_y.
      - inversion H.
      - inversion_clear H as [| p1 x1' x2' v' H1 | p2 x1' x2' v' H2].
        + destruct (join_left _ _ _ _ _ _ _ _ H1) as [p_x1 [p_y [H_p1 []]]].
          exists (Choose.Last.Path.ChooseLeft p_x1); exists p_y.
          rewrite H_p1.
          split; trivial.
          split; trivial.
          now apply Choose.Last.Eval.ChooseLeft.
        + destruct (join_left _ _ _ _ _ _ _ _ H2) as [p_x2 [p_y [H_p2 []]]].
          exists (Choose.Last.Path.ChooseRight p_x2); exists p_y.
          rewrite H_p2.
          split; trivial.
          split; trivial.
          now apply Choose.Last.Eval.ChooseRight.
    Qed.

    Fixpoint join_right {E A B} {p : Choose.Last.Path.t} {x : Choose.t E A}
      {y : Choose.t E B} {v_x : A} {v_y : B}
      (H : Choose.Last.Eval.t p (Choose.join_right x y) (v_x, v_y))
      : exists p_y, exists p_x,
        p = Choose.Last.Path.bind p_y p_x /\
        Choose.Last.Eval.t p_x x v_x /\
        Choose.Last.Eval.t p_y y v_y.
      destruct y; simpl in *.
      - exists Choose.Last.Path.Ret; exists p.
        split; trivial.
        destruct (map H) as [v'_x [H_x H_eq]].
        replace b with v_y by congruence.
        replace v_x with v'_x by congruence.
        split.
        + apply H_x.
        + apply Choose.Last.Eval.Ret.
      - inversion H.
      - inversion_clear H as [| p1 x1' x2' v' H1 | p2 x1' x2' v' H2].
        + destruct (join_right _ _ _ _ _ _ _ _ H1) as [p_y1 [p_x [H_p1 []]]].
          exists (Choose.Last.Path.ChooseLeft p_y1); exists p_x.
          rewrite H_p1.
          split; trivial.
          split; trivial.
          now apply Choose.Last.Eval.ChooseLeft.
        + destruct (join_right _ _ _ _ _ _ _ _ H2) as [p_y2 [p_x [H_p2 []]]].
          exists (Choose.Last.Path.ChooseRight p_y2); exists p_x.
          rewrite H_p2.
          split; trivial.
          split; trivial.
          now apply Choose.Last.Eval.ChooseRight.
    Qed.

    Fixpoint to_c {E A} {x : C.t E A} {v : A} {p_x p_k : Choose.Last.Path.t}
      (H : Choose.Last.Eval.t p_x (Compile.to_choose x) v)
      : exists p'_x,
          Compile.Path.Last.to_c x (Choose.Last.Path.bind p_x p_k) =
            Some (p'_x, v, p_k) /\
          C.Last.Eval.t p'_x x v.
      destruct x; simpl in *.
      - inversion_clear H.
        simpl.
        exists C.Last.Path.Ret.
        split.
        + reflexivity.
        + apply C.Last.Eval.Ret.
      - inversion H.
      - destruct (bind H) as [v_x [p_x_x [p_x_f [H_p_x [H_p_x_x H_p_x_f]]]]].
        rewrite <- H_p_x.
        destruct (to_c _ _ _ _ _ (Choose.Last.Path.bind p_x_f p_k) H_p_x_x)
          as [p'_x [H_x_x]].
        rewrite <- Choose.Last.Path.bind_assoc.
        destruct (to_c _ _ _ _ _ p_k H_p_x_f) as [p'_f [H_x_f]].
        rewrite H_x_x.
        rewrite H_x_f.
        eexists.
        split.
        + reflexivity.
        + now apply (C.Last.Eval.Let _ _ _ _ v_x).
      - destruct p_x as [|p_x | p_x].
        + destruct (choose H).
        + assert (H_x1 := choose H).
          simpl in *.
          destruct (to_c _ _ _ _ _ p_k H_x1) as [p'_x1 [H1]].
          rewrite H1.
          eexists.
          split.
          * reflexivity.
          * now apply C.Last.Eval.ChooseLeft.
        + assert (H_x2 := choose H).
          simpl in *.
          destruct (to_c _ _ _ _ _ p_k H_x2) as [p'_x2 [H2]].
          rewrite H2.
          eexists.
          split.
          * reflexivity.
          * now apply C.Last.Eval.ChooseRight.
      - assert (H_join := join H).
        destruct v as [v_x v_y].
        destruct p_x as [|p|].
        + destruct H_join.
        + destruct (join_left H_join) as [p_x [p_y [H_p [H_p_x H_p_y]]]].
          simpl.
          rewrite H_p.
          rewrite <- Choose.Last.Path.bind_assoc.
          destruct (to_c _ _ _ _ _ (Choose.Last.Path.bind p_y p_k) H_p_x) as
            [p'_x1 [H_x1]].
          rewrite H_x1.
          destruct (to_c _ _ _ _ _ p_k H_p_y) as [p'_x2 [H_x2]].
          rewrite H_x2.
          eexists.
          split.
          * reflexivity.
          * now apply C.Last.Eval.Join.
        + destruct (join_right H_join) as [p_y [p_x' [H_p [H_p_x H_p_y]]]].
          simpl.
          rewrite H_p.
          rewrite <- Choose.Last.Path.bind_assoc.
          destruct (to_c _ _ _ _ _ (Choose.Last.Path.bind p_x' p_k) H_p_y) as
            [p'_x1 [H_x1]].
          rewrite H_x1.
          destruct (to_c _ _ _ _ _ p_k H_p_x) as [p'_x2 [H_x2]].
          rewrite H_x2.
          eexists.
          split.
          * reflexivity.
          * now apply C.Last.Eval.Join.
    Qed.
  End Last.
End ToC.
