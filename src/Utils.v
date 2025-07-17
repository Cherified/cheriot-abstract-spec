(*! Utils *)
From Stdlib Require Import List Lia Bool Nat NArith.
From cheriot Require Import Tactics.
Import ListNotations.

Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).

Module Combinators.
  Section __.
    Context [State : Type] (step: State -> State -> Prop).
    Inductive always(P: State -> Prop)(initial: State): Prop :=
    | mk_always
        (invariant: State -> Prop)
        (Establish: invariant initial)
        (Preserve: forall s t, invariant s -> step s t -> invariant t)
        (Use: forall s, invariant s -> P s).

    (* P until Q *)
    Inductive until (P: State -> Prop) (Q: State -> Prop) (initial: State) : Prop :=
    | until_done:
      Q initial ->
      until P Q initial
    | until_step:
      P initial ->
      (forall mid, step initial mid -> until P Q mid) ->
      until P Q initial.

    (* Inductive eventually(P: State -> Prop)(initial: State): Prop := *)
    (* | eventually_done: *)
    (*       P initial -> *)
    (*       eventually P initial *)
    (* | eventually_step: *)
    (*       (forall mid, step initial mid -> eventually P mid) -> *)
    (*       eventually P initial. *)
  End __.
End Combinators.

Module Separation.
  Definition Disjoint {T: Type} (xs ys: list T) : Prop :=
    forall t, In t xs -> In t ys -> False.

  Definition Pairwise {T: Type} (P: T -> T -> Prop) (xss: list T) : Prop :=
    forall i j xi xj,
      i <> j ->
      nth_error xss i = Some xi ->
      nth_error xss j = Some xj ->
      P xi xj.

  Definition Separated {T: Type} (xss: list (list T)) : Prop :=
    Pairwise Disjoint xss.

End Separation.

Section EqSet.
  Context [A: Type].
  Variable l1 l2: list A.
  Definition EqSet := forall x, In x l1 <-> In x l2.

  Theorem Eq_imp_EqSet: l1 = l2 -> EqSet.
  Proof.
    unfold EqSet; intros; subst; tauto.
  Qed.

  Definition Subset := forall x, In x l1 -> In x l2.

End EqSet.

Inductive Result {e t} :=
| Ok : t -> Result
| Exn : e -> Result.
Arguments Result : clear implicits.

Ltac simplify_Result :=
  repeat match goal with
  | H: match ?x with | Ok _ => _ | Exn _ => False end |- _ =>
      let Ht := fresh H "Ok" in
      destruct x eqn:Ht; [ | contradiction]
  end.

Section Option.
  Definition is_some [A] (a: option A) : bool :=
    match a with
    | Some _ => true
    | _ => false
    end.


  Lemma Some_inj :
    forall A (x y:A),
    Some x = Some y ->
    x = y.
  Proof.
    intros. inversion H. auto.
  Qed.

  Lemma option_map_Some:
    forall {A B} (f: A -> B) xs b,
    option_map f xs = Some b ->
    exists a, xs = Some a /\ f a = b.
  Proof.
    cbv[option_map]. intros *. destruct xs; intros;
      repeat match goal with
      | H : Some ?x = Some _ |- _ => apply Some_inj in H; simplify_eq
      | H : None = Some _ |- _ => clear - H; discriminate
      end; eauto.
  Qed.

  Lemma Some_not_None :
    forall A (a: A) x,
      x = Some a ->
      x <> None.
  Proof.
    destruct x; congruence.
  Qed.

  Definition from_option {A B} (f : A -> B) (y : B) (mx : option A) : B :=
    match mx with None => y | Some x => f x end.

End Option.

Ltac option_simpl :=
  repeat match goal with
  | H : Some ?x = Some _ |- _ => apply Some_inj in H; simplify_eq
  | H : ?x = Some ?y, H1 : ?x = Some ?z |- _ => rewrite H in H1; apply Some_inj in H1; try subst y; try subst z
  | H : None = Some _ |- _ => clear - H; discriminate
  | H : Some _ = None  |- _ => clear - H; discriminate
  end.

Section Forall.
  Lemma Forall_one:
    forall {T} (x: T) P,
    Forall P [x] ->
    P x.
  Proof.
    inversion 1. auto.
  Qed.

  Lemma Forall2_refl {A: Type} (R: A -> A -> Prop) :
    forall xs,
    (forall a, R a a) ->
    Forall2 R xs xs.
  Proof.
    induction xs; auto.
  Qed.
  Lemma Forall2_nth_error1 : forall A B (R: A -> B -> Prop) xs ys,
      length xs = length ys ->
      (forall idx x y, nth_error xs idx = Some x ->
                  nth_error ys idx = Some y ->
                  R x y) ->
      Forall2 R xs ys.
  Proof.
    induction xs.
    - destruct ys; try discriminate; auto.
    - destruct ys; try discriminate.
      intros; constructor; eauto.
      + eapply H0 with (idx := 0); eauto.
      + eapply IHxs; eauto.
        intros; eapply H0 with (idx := S idx); auto.
  Qed.

  Lemma Forall2_nth_error2 : forall A B (R: A -> B -> Prop) xs ys,
      Forall2 R xs ys ->
      forall idx x y,
      nth_error xs idx = Some x ->
      nth_error ys idx = Some y ->
      R x y.
  Proof.
    induction 1.
    - intros *; rewrite nth_error_nil. discriminate.
    - destruct idx; cbn; intros;
        repeat match goal with
        | H: Some _ = Some _ |- _ => apply Some_inj in H; subst
        end; eauto.
  Qed.

  Lemma Forall2_nth_error2' : forall A B (R: A -> B -> Prop) xs ys idx,
      Forall2 R xs ys ->
      idx < length xs ->
      exists x y,
      nth_error xs idx = Some x /\
      nth_error ys idx = Some y /\
      R x y.
  Proof.
    intros.
    destruct (nth_error xs idx) eqn:?.
    destruct (nth_error ys idx) eqn:?.
    - exists a; exists b; repeat split; auto.
      eapply Forall2_nth_error2; eauto.
    - apply nth_error_None in Heqo0. rewrite Forall2_length with (1 := H) in H0. lia.
    - apply nth_error_None in Heqo. lia.
  Qed.
End Forall.

Ltac simplify_Forall :=
  repeat match goal with
  | H : Forall _ (_ ++ _ ) |- _ =>
      apply Forall_app in H;
      let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | H : Forall _ [_] |- _ =>
      apply Forall_one in H
  end.


Section Subset.
  Lemma SubsetFilter1:
    forall {A} (xs ys: list A) eqb,
    (forall p q, eqb p q = true -> p = q) ->
    Subset (filter (fun p => existsb (eqb p) xs) ys) xs.
  Proof.
    cbv[Subset]. intros * eqb *.
    rewrite filter_In, existsb_exists.
    intros; destruct_products; eauto.
    apply eqb in Hrr. subst; auto.
  Qed.

  Lemma Subset_app:
    forall {A} (xs ys: list A),
      Subset xs (xs ++ ys).
  Proof.
    cbv[Subset].
    intros. apply in_or_app. auto.
  Qed.

  Lemma Subset_refl :
    forall {A} (xs: list A),
      Subset xs xs.
  Proof.
    cbv[Subset]. auto.
  Qed.
End Subset.
Ltac simplify_Subset :=
  repeat match goal with
    | |- Subset ?x (?x ++ _) =>
        apply Subset_app
    | |- Subset ?x ?x =>
        apply Subset_refl
    end.

Section ListUpdate.
  Lemma listUpdate_length:
    forall A (xs ys: list A) idx a,
      (forall n, n <> idx -> nth_error ys n = nth_error xs n) ->
      idx < length xs ->
      nth_error ys idx = Some a ->
      length xs = length ys.
  Proof.
    intros * herror hlen hsome.
    destruct (PeanoNat.Nat.eq_dec (length xs) (length ys)); auto.
    exfalso.
    assert (length xs < length ys \/ length ys < length xs) as Hcase by lia.
    destruct_or! Hcase; exfalso.
    - rewrite<-nth_error_Some in Hcase.
      rewrite herror in Hcase by lia.
      rewrite nth_error_Some in Hcase. lia.
    - destruct_with_eqn (Nat.ltb idx (length ys)).
      + rewrite PeanoNat.Nat.ltb_lt in *.
        rewrite<-nth_error_Some in Hcase.
        rewrite<-herror in Hcase by lia.
        rewrite nth_error_Some in Hcase. lia.
      + rewrite PeanoNat.Nat.ltb_nlt in *.
        apply Some_not_None in hsome.
        apply nth_error_Some in hsome. lia.
  Qed.
End ListUpdate.

Lemma nth_error_Some' :
  forall [A: Type] (l: list A) (n: nat) (a: A),
    nth_error l n = Some a ->
    n < length l.
Proof.
  intros. eapply nth_error_Some. by eapply Some_not_None.
Qed.
Ltac saturate_list:=
  repeat match goal with
  | H: nth_error ?xs ?idx = Some _ |- _ =>
      let H' := fresh H "len" in 
      learn_hyp (nth_error_Some' _ _ _ H) as H'
  | H: nth_error ?xs ?idx = Some _ |- _ =>
      let H' := fresh H "In" in 
      learn_hyp (nth_error_In _ _ H) as H'
  | H: Forall2 _ _ _ |- _ =>
      let H' := fresh H "len" in 
      learn_hyp (Forall2_length H) as H'
    end.
Ltac unsafe_saturate_list :=
  saturate_list;
  repeat match goal with
  | H: In ?xs ?x |- _ =>
      lazymatch goal with
      | H': nth_error xs _ = Some x |- _ => fail 1
      | |- _ =>
          let H' := fresh H "nth_error" in
          learn_hyp (In_nth_error _ _ H) as H'
      end
  end.


Fixpoint listSumToInl [A B: Type] (l: list (A+B)) : list A :=
  match l with
  | nil => nil
  | x :: xs => match x with
               | inl y => y :: listSumToInl xs
               | _ => listSumToInl xs
               end
  end.
Lemma In_listSumToInl:
  forall A B (xs: list (A+B)) x,
  In (inl x) xs ->
  In x (listSumToInl xs).
Proof.
  induction xs; cbn; auto.
  intros * H. inv H; subst; auto.
  - constructor. auto.
  - apply IHxs in H0. case_match; [right | ]; auto.
Qed.
Lemma listSumToInl_In:
  forall A B (xs: list (A+B)) x,
  In x (listSumToInl xs) ->
  In (inl x) xs.
Proof.
  induction xs; cbn; auto.
  intros. case_match; subst.
  - inv H; auto.
  - apply IHxs in H. auto.
Qed.

Lemma listSumToInl_iff:
  forall A B (xs: list (A+B)) x,
  In x (listSumToInl xs) <->
  In (inl x) xs.
Proof.
  split.
  - apply listSumToInl_In.
  - apply In_listSumToInl.
Qed.

Theorem seqInBounds n: forall b v,
    b <= v < b + n -> In v (seq b n).
Proof.
  induction n; simpl; intros.
  - lia.
  - destruct (PeanoNat.Nat.eq_dec b v); [auto|right].
    apply IHn.
    lia.
Qed.

Ltac simplify_nat :=
  repeat match goal with
  | H: _ <? _ = true |- _ => rewrite PeanoNat.Nat.ltb_lt in H
  | H: _ <? _ = false |- _ => rewrite PeanoNat.Nat.ltb_nlt in H
  | _ => lia                                                                       
  end.
