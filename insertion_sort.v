From stdpp Require Import list orders.

Section Sorting.
  
  SearchAbout relation.
  
  Context {A : Type}.
  
  Context (R : relation A).
  
  Print PartialOrder.

  Print AntiSymm.

  Context `{TotalOrder A R}.

  Locate "≤".

  Notation "a ≤ b" := (R a b).

  Notation "a < b" := (strict R a b).

  (* This is one of many possible definitions of Sorted.
     It's a useful exercise to prove they are equivalent! *)
  Inductive Sorted : list A → Prop :=
  | nil_sorted : Sorted []
  | singleton_sorted : ∀ a, Sorted [a]
  | pair_sorted : ∀ a b l, a ≤ b → Sorted (b::l) → Sorted (a::b::l).

  Hint Constructors Sorted.

  Print RelDecision.

  Context `{RelDecision _ _ R}.

  Fixpoint insert (a : A) (l : list A) : list A :=
    match l with
    | [] => [a]
    | b::bs => if decide (a ≤ b) then a::l
               else b::(insert a bs)
    end.

  Fixpoint sort (l : list A) : list A :=
    match l with
    | [] => []
    | b :: bs => insert b (sort bs)
    end.

  (* Should use ints, so we can write a couple of tests here *)


  (* Our goal is this: *)
  Theorem sorted_sort : ∀ l, Sorted (sort l).
  Proof.
    induction l.
    - auto.
    - simpl. (* This is doomed to fail, but let's try anyways, to see how *)
      
      unfold insert.
      case_eq (sort l); auto.
      intros.
      destruct (decide (a ≤ a0)).
      + constructor; rewrite H1 in *; now auto.
      + fold insert.
  Abort.

  SearchAbout TotalOrder.
  Print Trichotomy.
  SearchAbout Trichotomy.

  (* Somehow this lemma is missing, but it's easy to prove for a total order *)
  Lemma antisym_neg : ∀ a b, ¬ a ≤ b → b ≤ a.
  Proof.
    intros.
    generalize (trichotomy _ a b);
      unfold strict; firstorder.
  Qed.

  Hint Resolve antisym_neg.
  
  Lemma sorted_insert : ∀ a l, Sorted l → Sorted (insert a l).
  Proof.
    intros a l srtd_l; induction srtd_l; simpl; auto.
    destruct (decide (a ≤ a0)); simpl; constructor; auto.
    destruct (decide (a ≤ a0)); auto.
    revert IHsrtd_l.
    unfold insert.
    destruct (decide (a ≤ b)); simpl; auto.
  Qed.

  Hint Resolve sorted_insert.

  Theorem sorted_sort : ∀ l, Sorted (sort l).
  Proof.
    induction l; simpl; auto.
  Qed.

  (* Same remark as for Sorted: there are many possible equivalent definitions here! *)
  Print Permutation.

  SearchAbout Permutation.

  Lemma perm_insert : ∀ a l l', l' ≡ₚ l → a::l' ≡ₚ insert a l.
  Proof.
    intros a l.
    induction l; simpl; intros; auto.
    destruct (decide (a ≤ a0)); auto.
    setoid_rewrite H1.
    setoid_rewrite Permutation_swap.
    constructor.
    apply IHl; auto.
  Qed.

  Theorem perm_sort : ∀ l, l ≡ₚ sort l.
  Proof.
    intro l; induction l; simpl; auto.
    apply perm_insert; auto.
  Qed.

End Sorting.


Check sort.


SearchAbout RelDecision.

Eval compute in (sort le [3;2;3;4;5;5;3;6;78;0;1]).
