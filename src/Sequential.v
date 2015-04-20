(** * Evaluation of concurrent computations in a sequential monad. *)
Require Import Io.All.
Require Import SmallSteps.

(** * Sequential computations. *)
Module S.
  Inductive t (E : Effect.t) : Type -> Type :=
  | Ret : forall {A : Type} (x : A), t E A
  | Call : forall (c : Effect.command E), t E (Effect.answer E c)
  | Let : forall (A B : Type), t E A -> (A -> t E B) -> t E B.
  Arguments Ret {E A} _.
  Arguments Call {E} _.
  Arguments Let {E A B} _ _.

  (** A nicer notation for `Ret`. *)
  Definition ret {E : Effect.t} {A : Type} (x : A) : t E A :=
    Ret x.

  (** A nicer notation for `Call`. *)
  Definition call (E : Effect.t) (c : Effect.command E)
    : t E (Effect.answer E c) :=
    Call (E := E) c.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Let`. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (Let X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (Let X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the unit answer. *)
    Notation "'do!' X 'in' Y" :=
      (Let X (fun (_ : unit) => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End S.

Module Run.
  Inductive t : forall {E : Effect.t} {A : Type}, S.t E A -> A -> Type :=
  | Ret : forall {E A} (x : A), t (S.Ret (E := E) x) x
  | Call : forall E (c : Effect.command E) (a : Effect.answer E c),
    t (S.Call (E := E) c) a
  | Let : forall {E A B} {c_x : S.t E A} {x : A} {c_f : A -> S.t E B} {y : B},
    t c_x x -> t (c_f x) y -> t (S.Let c_x c_f) y.
End Run.

Module Eval.
  Import S.Notations.

  Module Choose.
    Inductive t : Set :=
    | Abort
    | Choose.

    Definition answer (c : t) : Type :=
      match c with
      | Abort => Empty_set
      | Choose => bool 
      end.

    Definition E : Effect.t :=
      Effect.New t answer.

    Definition abort {A : Type} : S.t E A :=
      let! x := S.call E Abort in
      match x with end.

    Definition choose : S.t E bool :=
      S.call E Choose.
  End Choose.

  Fixpoint value {E A} (x : C.t E A) : S.t Choose.E A :=
    match x with
    | C.Ret _ v => S.ret v
    | C.Call _ => Choose.abort
    | C.Let _ _ x f =>
      let! x := value x in
      value (f x)
    | C.Choose _ x1 x2 =>
      let! choice := Choose.choose in
      if choice then
        value x1
      else
        value x2
    | C.Join _ _ x y =>
      let! x := value x in
      let! y := value y in
      S.ret (x, y)
    end.

  Fixpoint of_last_step {E A} (x : C.t E A) (v : A) (last_step : LastStep.t x v)
    : Run.t (value x) v.
    destruct last_step; simpl.
    - apply Run.Ret.
    - eapply Run.Let.
      + apply of_last_step.
        apply last_step1.
      + now apply of_last_step.
    - eapply Run.Let.
      + apply (Run.Call Choose.E Choose.Choose true).
      + now apply of_last_step.
    - eapply Run.Let.
      + apply (Run.Call Choose.E Choose.Choose false).
      + now apply of_last_step.
    - eapply Run.Let.
      + apply of_last_step.
        apply last_step1.
      + eapply Run.Let.
        * apply of_last_step.
          apply last_step2.
        * apply Run.Ret.
  Defined.

  (*Definition gre {E A} (v v' : A) (last_step : LastStep.t (C.Ret E v) v') : v = v'.
    refine (match last_step in LastStep.t (A := A) x v'' return
      match x with
      | C.Ret _ v''' => v''' = v'''
      | _ => True
      end with
    | LastStep.Ret _ _ => _
    | _ => I
    end).
    inversion last_step.
  Qed.

  Fixpoint to_last_step {E A} (x : C.t E A) : forall (v : A) (run : Run.t (value x) v),
    LastStep.t x v.
    refine (
      match x in C.t _ A return
        forall (v : A), Run.t (value x) v -> LastStep.t x v with
      | C.Ret _ v => _
      | C.Call _ => _
      | C.Let _ _ x f => _
      | C.Choose _ x1 x2 => _
      | C.Join _ _ x y => _
      end); simpl; intros v' run.
    - Eval cbv in (match S.ret v with
  | S.Ret A1 v => LastStep.t (C.Ret E v') v'
  | S.Call _ => LastStep.t (C.Ret E v') v'
  | S.Let _ _ _ _ => LastStep.t (C.Ret E v') v'
  end).
      refine (
        match run in Run.t x v return
          match x with
          | S.Ret _ v => LastStep.t (C.Ret E v) v
          | _ => LastStep.t (C.Ret E v) v
          end with
        | Run.Ret _ _ v => _
        | _ => _
        end).
    
    inversion_clear run.
    - 
  Defined.

  Fixpoint to_last_step {E A} (x : C.t E A)
    : forall (v : A) (run : Run.t (value x) v), LastStep.t x v.
    refine (
      match x with
      | 
      end).
    destruct x; intros v run.
    - inversion run.
    apply LastStep.Ret.
  Defined.*)
End Eval.
