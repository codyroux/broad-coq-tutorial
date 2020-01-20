From Coq Require Import List Lia Arith Permutation.

Import ListNotations.

Section Sorting.

  Check (list nat).

  (* This is one of many possible definitions of Sorted.
     It's a useful exercise to prove they are equivalent! *)
  Inductive Sorted : list nat -> Prop :=
  | nil_sorted : Sorted []
  | singleton_sorted : forall a, Sorted [a]
  | pair_sorted : forall a b l, a <= b -> Sorted (b::l) -> Sorted (a::b::l).

  Hint Constructors Sorted.

  Fixpoint insert (a : nat) (l : list nat) : list nat :=
    match l with
    | [] => [a]
    | b::bs => if (a <=? b) then a::l
               else b::(insert a bs)
    end.

  Fixpoint sort (l : list nat) : list nat :=
    match l with
    | [] => []
    | b :: bs => insert b (sort bs)
    end.

  Eval compute in (sort [3;4;5;2;5;6;3;2;2;46;87;8;0]).

  SearchAbout (_ <=? _).
  SearchAbout (BoolSpec).
  SearchAbout Bool.reflect.

  SearchAbout (_ < _ -> _ <= _).

  Hint Resolve Nat.lt_le_incl.

  (* Our goal is this: *)
  Theorem sorted_sort : forall l, Sorted (sort l).
  Proof.
    induction l.
    - auto.
    - simpl. (* This is doomed to fail, but let's try anyways, to see how *)

      unfold insert.
      case_eq (sort l); auto.
      intros a0 l0 H1.
      destruct (Nat.leb_spec a a0).
      + constructor; rewrite H1 in *; now auto.
      + fold insert.
  Abort.

  Lemma sorted_insert : forall a l, Sorted l -> Sorted (insert a l).
  Proof.
    intros a l srtd_l; induction srtd_l; simpl; auto.
    destruct (Nat.leb_spec a a0); simpl; constructor; auto; lia.
    destruct (Nat.leb_spec a a0); auto.
    revert IHsrtd_l.
    unfold insert.
    destruct (Nat.leb_spec a b); simpl; auto.
  Qed.

  Hint Resolve sorted_insert.

  Theorem sorted_sort : forall l, Sorted (sort l).
  Proof.
    induction l; simpl; auto.
  Qed.

  (* Same remark as for Sorted: there are many possible equivalent definitions here! *)
  Print Permutation.

  SearchAbout Permutation.

  Notation "l1 ~ l2" := (Permutation l1 l2)(at level 80).

  Lemma perm_insert : forall a l l', l' ~ l -> a::l' ~ insert a l.
  Proof.
    intros a l.
    induction l; simpl; intros l' H; auto.
    destruct (Nat.leb_spec a a0); auto.
    setoid_rewrite H.
    setoid_rewrite perm_swap.
    constructor.
    apply IHl; auto.
  Qed.

  Hint Resolve perm_insert.

  Theorem perm_sort : forall l, l ~ sort l.
  Proof.
    intro l; induction l; simpl; auto.
  Qed.

End Sorting.
