From Coq Require Import List Lia Arith Permutation.

Import ListNotations.

(* Let's try to verify a simple sorting algorithm! *)
(* If anyone wants to know why one would verify such a simple thing, try googling "timsort bug"... *)
Section Sorting.

  Check (list nat).

  (* This is one of many possible definitions of Sorted.
     It's a useful exercise to prove they are equivalent! *)
  Inductive Sorted : list nat -> Prop :=
  | nil_sorted : Sorted []
  | singleton_sorted : forall a, Sorted [a]
  | pair_sorted : forall a b l, a <= b -> Sorted (b::l) -> Sorted (a::b::l).

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

  (* Search (_ <=? _). *)
  (* Search (BoolSpec). *)
  (* Search Bool.reflect. *)

  (* Search (_ < _ -> _ <= _). *)

  (* Our goal is this: *)
  Theorem sorted_sort : forall l, Sorted (sort l).
  Proof.
  Abort.

  (* If you're struggling, that's normal! We need an extra lemma to make this proof go through... *)


  (* Same remark as for Sorted: there are many possible equivalent definitions here! *)
  Print Permutation.

  (* Search Permutation. *)

  Notation "l1 ~ l2" := (Permutation l1 l2)(at level 80).

  Theorem perm_sort : forall l, l ~ sort l.
  Proof.
  Abort.

End Sorting.
