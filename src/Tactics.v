From Stdlib Require Import List Lia Bool Nat NArith.

Lemma simple_tuple_inversion:
  forall {A} {B} (a: A) (b: B) x y,
  (a,b) = (x,y) ->
  a = x /\ b = y.
Proof.
  intros. inversion H. auto.
Qed.

Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : False |- _ => contradiction
  | H : ?x = _ |- _ => subst x
  | H: _ = ?x |- _ => subst x
  | [ H: (_,_) = (_,_) |- _ ] =>
    apply simple_tuple_inversion in H;
    let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  end.

Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
      repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
      repl_match_hyp H d d'
  end.
Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  | H: context[let '(_,_) := ?x in _] |- _ =>
    destruct x eqn:?
  | |- context[let '(_,_) := ?x in _] =>
    destruct x eqn:?
  end.

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | _ =>
      destruct e eqn:?
  end.

Ltac destruct_matches_in_hyp H :=
  lazymatch type of H with
  | context[match ?d with | _ => _ end] =>
      destruct_matches_in d
  | ?v =>
      let H1 := fresh H in
      destruct v eqn:H1
  end.

Tactic Notation "case_match" "eqn" ":" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.
Ltac case_match :=
  let H := fresh in case_match eqn:H.
Ltac simplify_nats :=
  match goal with
  | H: Nat.eqb _ _ = true |- _ =>
      rewrite PeanoNat.Nat.eqb_eq in H
  | H: Nat.eqb _ _ = false |- _ =>
      rewrite PeanoNat.Nat.eqb_neq in H
  end.
Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | reflexivity ].
Tactic Notation "fast_by" tactic(tac) :=
  tac; fast_done.
Ltac done :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    | progress intros
    | solve [symmetry; trivial]
    | discriminate
    | contradiction
    | split
    ]
  ].
Tactic Notation "by" tactic(tac) :=
  tac; done.
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ \/ _ => destruct H as [H|H]
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.
Tactic Notation "split_and" :=
  match goal with
  | |- _/\ _ => split
  end.
Tactic Notation "split_and" "?" := repeat split_and.
Tactic Notation "split_and" "!" := hnf; split_and; split_and?.
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ \/ _ => destruct H as [H|H]
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.

Ltac consider X :=
  unfold X in *.

Ltac propositional :=
  repeat match goal with
  | H1: ?x -> _, H2: ?x |- _ =>
      specialize H1 with (1 := H2)
  end.
Ltac assert_pre_and_specialize H :=
  match type of H with
  | ?x -> _ => let Hx := fresh in assert x as Hx; [ | specialize H with (1 := Hx); clear Hx]
  end.

Ltac rewrite_solve :=
  match goal with
  | [ H: _ |- _ ] => solve[rewrite H; try congruence; auto]
  end.
