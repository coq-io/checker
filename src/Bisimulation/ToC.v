Require Import Io.All.
Require Choose.
Require Compile.
Require Import Semantics.

Module Last.
  Fixpoint map {E A B} {p : Choose.Path.t} {x : Choose.t E A}
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
    {p : Choose.Path.t} (H : Choose.Last.Eval.t p (Choose.bind x f) v_y)
    : exists v_x, exists p_x, exists p_f,
      Choose.Path.bind p_x p_f = p /\
      Choose.Last.Eval.t p_x x v_x /\
      Choose.Last.Eval.t p_f (f v_x) v_y.
    destruct x; simpl in *.
    - exists a; exists Choose.Path.Done; exists p.
      split.
      + reflexivity.
      + split.
        * apply Choose.Last.Eval.Ret.
        * trivial.
    - inversion H.
    - inversion_clear H as [| p1 x1' x2' v' H1 | p2 x1' x2' v' H2].
      + destruct (bind _ _ _ _ _ _ _ H1) as [v_x [p_x [p_f [H_p1 [H_x1]]]]].
        exists v_x; exists (Choose.Path.ChooseLeft p_x); exists p_f.
        simpl.
        rewrite H_p1.
        split; trivial.
        split; trivial.
        now apply Choose.Last.Eval.ChooseLeft.
      + destruct (bind _ _ _ _ _ _ _ H2) as [v_x [p_x [p_f [H_p2 [H_x2]]]]].
        exists v_x; exists (Choose.Path.ChooseRight p_x); exists p_f.
        simpl.
        rewrite H_p2.
        split; trivial.
        split; trivial.
        now apply Choose.Last.Eval.ChooseRight.
  Qed.

  Fixpoint choose {E A} {p_x : Choose.Path.t} {x1 x2 : Choose.t E A}
    {v : A} (H : Choose.Last.Eval.t p_x (Choose.Choose x1 x2) v)
    : match p_x with
      | Choose.Path.Done => False
      | Choose.Path.ChooseLeft p_x => Choose.Last.Eval.t p_x x1 v
      | Choose.Path.ChooseRight p_x => Choose.Last.Eval.t p_x x2 v
      end.
    now inversion H.
  Qed.

  Fixpoint join {E A B} {p : Choose.Path.t} {x : Choose.t E A}
    {y : Choose.t E B} {v} (H : Choose.Last.Eval.t p (Choose.join x y) v)
    : match p with
      | Choose.Path.Done => False
      | Choose.Path.ChooseLeft p =>
        Choose.Last.Eval.t p (Choose.join_left x y) v
      | Choose.Path.ChooseRight p =>
        Choose.Last.Eval.t p (Choose.join_right x y) v
      end.
    now inversion_clear H.
  Qed.

  Fixpoint join_left {E A B} {p : Choose.Path.t} {x : Choose.t E A}
    {y : Choose.t E B} {v_x : A} {v_y : B}
    (H : Choose.Last.Eval.t p (Choose.join_left x y) (v_x, v_y))
    : exists p_x, exists p_y,
      p = Choose.Path.bind p_x p_y /\
      Choose.Last.Eval.t p_x x v_x /\
      Choose.Last.Eval.t p_y y v_y.
    destruct x; unfold Choose.join_left in *; simpl in *.
    - exists Choose.Path.Done; exists p.
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
        exists (Choose.Path.ChooseLeft p_x1); exists p_y.
        rewrite H_p1.
        split; trivial.
        split; trivial.
        now apply Choose.Last.Eval.ChooseLeft.
      + destruct (join_left _ _ _ _ _ _ _ _ H2) as [p_x2 [p_y [H_p2 []]]].
        exists (Choose.Path.ChooseRight p_x2); exists p_y.
        rewrite H_p2.
        split; trivial.
        split; trivial.
        now apply Choose.Last.Eval.ChooseRight.
  Qed.

  Fixpoint join_right {E A B} {p : Choose.Path.t} {x : Choose.t E A}
    {y : Choose.t E B} {v_x : A} {v_y : B}
    (H : Choose.Last.Eval.t p (Choose.join_right x y) (v_x, v_y))
    : exists p_y, exists p_x,
      p = Choose.Path.bind p_y p_x /\
      Choose.Last.Eval.t p_x x v_x /\
      Choose.Last.Eval.t p_y y v_y.
    destruct y; simpl in *.
    - exists Choose.Path.Done; exists p.
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
        exists (Choose.Path.ChooseLeft p_y1); exists p_x.
        rewrite H_p1.
        split; trivial.
        split; trivial.
        now apply Choose.Last.Eval.ChooseLeft.
      + destruct (join_right _ _ _ _ _ _ _ _ H2) as [p_y2 [p_x [H_p2 []]]].
        exists (Choose.Path.ChooseRight p_y2); exists p_x.
        rewrite H_p2.
        split; trivial.
        split; trivial.
        now apply Choose.Last.Eval.ChooseRight.
  Qed.

  Fixpoint to_c {E A} {x : C.t E A} {v : A} {p_x} (p_k : Choose.Path.t)
    (H : Choose.Last.Eval.t p_x (Compile.to_choose x) v)
    : exists p'_x,
        Compile.Path.to_c x (Choose.Path.bind p_x p_k) =
          inl (p'_x, v, p_k) /\
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
      destruct (to_c _ _ _ _ _ (Choose.Path.bind p_x_f p_k) H_p_x_x)
        as [p'_x [H_x_x]].
      rewrite <- Choose.Path.bind_assoc.
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
        rewrite <- Choose.Path.bind_assoc.
        destruct (to_c _ _ _ _ _ (Choose.Path.bind p_y p_k) H_p_x) as
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
        rewrite <- Choose.Path.bind_assoc.
        destruct (to_c _ _ _ _ _ (Choose.Path.bind p_x' p_k) H_p_y) as
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

Fixpoint gre {E c c' a A} {h'} {x' : Choose.t E A}
  (H : Choose.Eval.t c a Choose.Path.Done (Choose.Call c' h') x')
  : exists h, Choose.Eval.t c a Choose.Path.Done (Choose.Call c h) x'.
  inversion H.
  (*refine (
    match H in Choose.Eval.t _ _ _ x _ return
      match x with
      | Choose.Call c h =>
Qed.*)
Admitted.

(*Fixpoint map {E c a A B} {p : Choose.Path.t} {x : Choose.t E A} {f : A -> B}
  {y : Choose.t E B} {g : B -> C} (H : Choose.Eval.t c a p (Choose.map x f) y)
  : 
  : exists x', Choose.Eval.t c a p x x' /\ y = Choose.map x' f.*)

(*Fixpoint map {E c a A B} {p : Choose.Path.t} {x : Choose.t E A} {f : A -> B}
  {y : Choose.t E B} (H : Choose.Eval.t c a p (Choose.map x f) y)
  : exists x', Choose.Eval.t c a p x x' /\ y = Choose.map x' f.
  destruct p; simpl in *.
  - inversion_clear H.
    exists 
  inversion H.
  - destruct x; simpl in H2; try congruence.
    assert (c = c0) by admit.
    assert (t' := t).
    rewrite <- H3 in t'.
    exists (t' a).
    
    exists h.
  destruct x; simpl in *.
  - inversion H.
  - assert (exists h : Effect.answer E c -> Choose.t E B,
      Choose.Call c0 (fun a0 => Choose.map (t a0) f) = Choose.Call c h).
    refine (
      match H in Choose.Eval.t _ _ _ x _ return
        match x with
        | Choose.Call c' h' =>
          exists h, Choose.Call c' h = Choose.Call c h'
        | _ => True
        end : Prop with
      | Choose.Eval.Call _ => _
      | _ => I
      end).
    rewrite H0.
    exists (Choose.map (t a) f).
    destruct p; try inversion_clear H.
    eexists.
    split.
    + apply (Choose.Eval.Call c a).
Qed.*)

(* True but maybe not usefull. *)
Fixpoint map {E c a A B} {p : Choose.Path.t} {x x' : Choose.t E A}
  (f : A -> B) (H : Choose.Eval.t c a p x x')
  : Choose.Eval.t c a p (Choose.map x f) (Choose.map x' f).
  destruct p; inversion_clear H; simpl.
  - apply (Choose.Eval.Call c a).
  - apply Choose.Eval.ChooseLeft.
    now apply map.
  - apply Choose.Eval.ChooseRight.
    now apply map.
Qed.

Fixpoint bind {E c a A B} {p : Choose.Path.t} {x : Choose.t E A}
  {f : A -> Choose.t E B} {y : Choose.t E B}
  (H : Choose.Eval.t c a p (Choose.bind x f) y)
  : (exists p_x, exists v_x, exists p_f,
      Choose.Last.Eval.t p_x x v_x /\ Choose.Eval.t c a p_f (f v_x) y /\
        p = Choose.Path.bind p_x p_f) \/
    (exists x', Choose.Eval.t c a p x x' /\ y = Choose.bind x' f).
Admitted.

Fixpoint choose {E c a A} {p : Choose.Path.t} {x1 x2 x' : Choose.t E A}
  (H : Choose.Eval.t c a p (Choose.Choose x1 x2) x')
  : match p with
    | Choose.Path.Done => False
    | Choose.Path.ChooseLeft p => Choose.Eval.t c a p x1 x'
    | Choose.Path.ChooseRight p => Choose.Eval.t c a p x2 x'
    end.
Admitted.

Fixpoint join {E c a A B} {p : Choose.Path.t} {x1 : Choose.t E A}
  {x2 : Choose.t E B} {x'} (H : Choose.Eval.t c a p (Choose.join x1 x2) x')
  : match p with
    | Choose.Path.Done => False
    | Choose.Path.ChooseLeft p =>
      Choose.Eval.t c a p (Choose.join_left x1 x2) x'
    | Choose.Path.ChooseRight p =>
      Choose.Eval.t c a p (Choose.join_right x1 x2) x'
    end.
  now inversion_clear H.
Qed.

(*Fixpoint join_left {E c a A B} {p : Choose.Path.t} {x1 : Choose.t E A}
  {x2 : Choose.t E B} {x'}
  (H : Choose.Eval.t c a p (Choose.join_left x1 x2) x')
  : (exists p1, exists v1, exists p2,
      Choose.Last.Eval.t p1 x1 v1 /\
      Choose.Eval.t c a p2 (Choose.map x2 (fun v2 => (v1, v2))) x' /\
      p = Choose.Path.bind p1 p2) \/
    (exists x'1,
      Choose.Eval.t c a p x1 x'1 /\
      Choose.join x'1 x2 = x').
  destruct p.
  - destruct x1.
    + unfold Choose.join_left in *; simpl in *.
      left.
      exists Choose.Path.Done, a0, Choose.Path.Done.
      admit.
    + right.
      
      
    inversion_clear H.*)

Lemma rewrite_call {E : Effect.t} {c c' : Effect.command E} (H : c = c')
  {A : Type} (h : Effect.answer E c -> Choose.t E A)
  : exists h', Choose.Call c h = Choose.Call c' h'.
  exists (eq_rect c (fun c' => Effect.answer E c' -> _) h _ H).
  exact (
    match H in eq _ c' return
      Choose.Call c h = Choose.Call c' (eq_rect c _ h c' H) with
    | eq_refl => eq_refl
    end).
Qed.

Lemma falso : False.
Admitted.

Fixpoint join_left {E c a A B} {p : Choose.Path.t} {x1 : Choose.t E A}
  {x2 : Choose.t E B} {x'}
  (H : Choose.Eval.t c a p (Choose.join_left x1 x2) x')
  : (exists p1, exists v1, exists p2,
      Choose.Last.Eval.t p1 x1 v1 /\
      Choose.Eval.t c a p2 (Choose.map x2 (fun v2 => (v1, v2))) x' /\
      p = Choose.Path.bind p1 p2) \/
    (exists x'1,
      Choose.Eval.t c a p x1 x'1 /\
      Choose.join x'1 x2 = x').
  destruct x1; unfold Choose.join_left in *; simpl in *.
  - left.
    exists Choose.Path.Done, a0, p.
    split; [apply Choose.Last.Eval.Ret |].
    split; [apply H | reflexivity].
  - right.
    destruct falso.
  - inversion_clear H.
    + destruct (join_left _ _ _ _ _ _ _ _ _ H0).
      * left.
        destruct H as [p1 [v1 [p2 [H1 [H2 H3]]]]].
        exists (Choose.Path.ChooseLeft p1), v1, p2.
        split; [now apply Choose.Last.Eval.ChooseLeft |].
        split; trivial.
        now rewrite H3.
      * right.
        destruct H as [x'1 [H1 H2]].
        exists x'1.
        split; trivial.
        now apply Choose.Eval.ChooseLeft.
    + destruct (join_left _ _ _ _ _ _ _ _ _ H0).
      * left.
        destruct H as [p1 [v1 [p2 [H1 [H2 H3]]]]].
        exists (Choose.Path.ChooseRight p1), v1, p2.
        split; [now apply Choose.Last.Eval.ChooseRight |].
        split; trivial.
        now rewrite H3.
      * right.
        destruct H as [x'1 [H1 H2]].
        exists x'1.
        split; trivial.
        now apply Choose.Eval.ChooseRight.
Qed.

(*Fixpoint join_left {E c a A B} {p : Choose.Path.t} {x1 : Choose.t E A}
  {x2 : Choose.t E B} {x'}
  (H : Choose.Eval.t c a p (Choose.join_left x1 x2) x')
  : (exists p1, exists v1, exists p2,
      Choose.Last.Eval.t p1 x1 v1 /\
      Choose.Eval.t c a p2 (Choose.map x2 (fun v2 => (v1, v2))) x' /\
      p = Choose.Path.bind p1 p2) \/
    (exists x'1,
      Choose.Eval.t c a p x1 x'1 /\
      Choose.join x'1 x2 = x').
  destruct x1; unfold Choose.join_left in *; simpl in *.
  - left.
    exists Choose.Path.Done, a0, p.
    split; [apply Choose.Last.Eval.Ret |].
    split; [apply H | reflexivity].
  - right.
    assert (H_join : Choose.Eval.t c a p
      (Choose.Call c0
         (fun a0 => Choose.join (t a0) x2)) x').
    exact H.
    inversion H_join.
    refine (let t' :=
      eq_rect c0 (fun c => Effect.answer E c -> _) t _ (eq_sym H2) in _).
    assert (H_call : Choose.Call c0 t = Choose.Call c t') by admit.
    assert (H_call_join : Choose.Call c0
      (fun a0 : answer E c0 => Choose.join (t a0) x2) =
      Choose.Call c (fun a => Choose.join (t' a) x2)) by admit.
    rewrite H_call.
    rewrite H_call_join in H_join.
    exists (t' a).
    split.
    + apply Choose.Eval.Call.
    + rewrite H1.
      refine (
        match H_join in Choose.Eval.t _ _ _ x x' return
          match x with
          | Choose.Call c h =>
            (*Choose.join (t' a) x2*)h a = x'
          | _ => True
          end : Prop with
        | Choose.Eval.Call _ => _
        | _ => I
        end).
      reflexivity.
intuition.
      inversion_clear H_join.
intuition.
intuition.
      

    destruct (rewrite_call (eq_sym H2)
      (fun a0 => Choose.join (t a0) x2)) as [h' H_h'].
    rewrite H_h' in H_join.
    assert (H_join' : Choose.Eval.t c a p
      (Choose.Call c
         (fun a => Choose.join (t a) x2)) x').
    inversion H_join.
    destruct (rewrite_call (eq_sym H2) t) as [h H_h].
    exists (h a).
    split.
    + rewrite H_h.
      apply Choose.Eval.Call.
    + 
      
    exists (rewrite_call ).
    split.
    + rewrite H_call.
      inversion_clear H.
      apply Choose.Eval.Call.
    + 
    assert (H' : exists h,
      Choose.Eval.t c a p (Choose.Call c (fun a => Choose.join (h a) x2)) x').
    refine (
      match H in Choose.Eval.t _ _ _ x _ return
        match x with
        | Choose.Call c' h' =>
          exists h,
      Choose.Eval.t c a p (Choose.Call c (fun a => Choose.join (h a) x2)) x'
        | _ => True
        end : Prop with
      | Choose.Eval.Call _ => _
      | _ => I
      end).
    
    inversion H.
    exists x'.
    exists (t c0).
    split.
    + 
    
    Check map H.
    exists (Choose.Ret a0).
    split.
    + apply Choose.Eval.Ret.
    + 
Qed.*)

Fixpoint to_c {E c a A} {x : C.t E A} {x' : Choose.t E A} {p : Choose.Path.t}
  (H : Choose.Eval.t c a p (Compile.to_choose x) x')
  : exists p', exists x'',
      Compile.Path.to_c x p = inr p' /\
      C.Eval.t c a p' x x''.
  destruct x; simpl in *.
  - inversion H.
  - replace command with c.
    + exists C.Path.Call, (C.Ret _ a).
      split.
      * reflexivity.
      * apply C.Eval.Call.
    + exact (
        match H in Choose.Eval.t _ _ _ x _ return
          match x with
          | Choose.Call c' _ => c = c'
          | _ => True
          end : Prop with
        | Choose.Eval.Call _ => eq_refl
        | _ => I
        end).
  - destruct (bind H) as
      [[p_x [v_x [p_f [H_x [H_f H_p]]]]] | [x'' [H_x H_y]]].
    + rewrite H_p.
      destruct (Last.to_c p_f H_x) as [p'_x [H'_x]].
      rewrite H'_x.
      destruct (to_c _ _ _ _ _ _ _ H_f) as [p'_f [x'' [H'_f]]].
      rewrite H'_f.
      exists (C.Path.LetDone p'_x p'_f); exists x''.
      split.
      * reflexivity.
      * now apply (C.Eval.LetDone _ _ _ _ _ _ v_x).
    + destruct (to_c _ _ _ _ _ _ _ H_x) as [p'_x [x''' [H'_x]]].
      rewrite H'_x.
      exists (C.Path.Let p'_x); exists (C.Let _ _ x''' t).
      split.
      * reflexivity.
      * now apply C.Eval.Let.
  - assert (H_choose := choose H).
    destruct p as [|p|p].
    + destruct H_choose.
    + destruct (to_c _ _ _ _ _ _ _ H_choose) as [p'_x1 [x'' [H_x1]]].
      rewrite H_x1.
      exists (C.Path.ChooseLeft p'_x1); exists x''.
      split.
      * reflexivity.
      * now apply C.Eval.ChooseLeft.
    + destruct (to_c _ _ _ _ _ _ _ H_choose) as [p'_x2 [x'' [H_x2]]].
      rewrite H_x2.
      exists (C.Path.ChooseRight p'_x2); exists x''.
      split.
      * reflexivity.
      * now apply C.Eval.ChooseRight.
  - assert (H_join := join H).
    destruct p as [|p|p].
    + destruct H_join.
    + destruct (join_left H_join) as [[p1 [v1 [p2 [H1 [H2 H3]]]]] |
        [x'1 [H_x'1 H_eq]]].
      * 
      * destruct (to_c _ _ _ _ _ _ _ H_x'1) as [p'_x1 [x''1 [H'_x'1]]].
        rewrite H'_x'1.
        exists (C.Path.JoinLeft p'_x1); exists (C.Join _ _ x''1 x2).
        split; [reflexivity | now apply C.Eval.JoinLeft].
    + 
Qed.
