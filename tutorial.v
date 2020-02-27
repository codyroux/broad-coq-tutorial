(* Copy paste this whole buffer in https://x80.org/collacoq/ to run interactively *)
From Coq Require Import Bool.

Section Basics.

  (* At its core, Coq is a *typed* programing language *)
  (* There are a few (not many!) built-in types *)
  Check 3.
  Check 3 + 4.
  Check true.
  Check (true && false).

  (* And so it can evaluate programs *)
  Eval compute in 3 + 4.
  Eval compute in (true && false).

  (* Every top-level command starts with a capital letter and ends with a period. *)
  (* Grammar was very important to the original implementers... *)

  (* No side effects though, so no printing, scanning or reading from a file! *)
  Fail Check print.

  (* There are good reasons for this, which we will go into later *)

  (* We can define types. This is a simple sum type *)
  Inductive week_day :=
  | Monday : week_day
  | Tuesday : week_day
  | Wednesday : week_day
  | Thursday : week_day
  | Friday : week_day
  | Saturday : week_day
  | Sunday : week_day.

  (* And we can define functions *)
  Definition add_one (x : nat) : nat := x + 1.
  Definition return_monday (w : week_day) : week_day := Monday.

  Check add_one.
  Check return_monday.

  (* We can work by cases over sum types. *)
  Definition is_monday (w : week_day) : bool :=
    match w with
    | Monday => true
    | _ => false
    end.

  Check is_monday.

  Eval compute in (is_monday Tuesday).

  (* There is a powerful search feature, which takes types and returns
     potentially useful functions with similar types *)
  (* Sadly, this does not work in the online version... *)
  (* Search (bool -> bool). *)

  (* We can define types which may be recursive, e.g. the type of lists *)
  Inductive week_day_list :=
  | Nil : week_day_list
  | Cons : week_day -> week_day_list -> week_day_list.

  Check (Cons Monday (Cons Tuesday Nil)).

  (* Ok, we have lisp-style lists. Can we define car? *)
  Definition car (l : week_day_list) (default : week_day) : week_day :=
    match l with
    | Nil => default
    | Cons w _ => w
    end.
  (* We need a default value! A little unfortunate... but the price of being pure! *)

  (* How about cdr? *)
  Definition cdr (l : week_day_list) : week_day_list :=
    match l with
    | Nil => Nil
    | Cons _ l' => l'
    end.

  (* List notation a la lisp is tedious. Gladly, Coq's notation system is incredibly powerful! *)

  Notation "[ ]" := Nil.

  Notation "[ w ]" := (Cons w Nil).

  Notation "[ w1 ; w2 ; .. ; wn ]" := (Cons w1 (Cons w2 .. (Cons wn Nil) .. )).

  Definition work_week := [Monday; Tuesday; Wednesday; Thursday; Friday].

  (* All right, let's define some funner things. *)

  Definition eq_wd (w1 w2 : week_day) : bool :=
    match (w1, w2) with
    | (Monday,Monday) => true
    | (Tuesday,Tuesday) => true
    | (Wednesday,Wednesday) => true
    | (Thursday,Thursday) => true
    | (Friday,Friday) => true
    | (Saturday,Saturday) => true
    | (Sunday,Sunday) => true
    | _ => false
    end.


  Notation "w1 == w2" := (eq_wd w1 w2)(at level 10).

  (* How about a length function? This requires a special syntax: *)
  Fixpoint length (l : week_day_list) : nat :=
    match l with
    | [] => 0
    | Cons w ws => (length ws) + 1
    end.

  Eval compute in (length work_week).

  (* Now let's define a membership function *)
  Fixpoint is_a_member (w : week_day) (l : week_day_list) : bool :=
    match l with
    | [] => false
    | Cons w' ws => if w == w' then true else is_a_member w ws
    end.

  (* Let's test it: *)
  Eval compute in (is_a_member Monday work_week).
  Eval compute in (is_a_member Sunday work_week).

  (* Ok, we're ready for some specifications! *)
  (* The simplest kind of specification is equality: *)
  Check (Monday = Monday).

  (* The Prop type is the type of *specifications*. It is *not* bool! *)
  Check (forall w : week_day, w = Monday).
  Check (exists w : week_day, w = Monday).

  (* The basic  propositional connectives: *)
  (* True. Always satisfied. *)
  (* False. Never satisfied. *)
  (* P\/Q. Satisfied if one of P or Q (or both) is satisfied. *)
  (* P/\Q. Satisfied if both P and Q are satisfied. *)
  (* P -> Q. Satisfied if, when *assuming* P is satisfied, then so is Q. *)
  (* ~P. Satisfied if P is *never* satisfied *)
  (* forall x : A, P x. Satisfied if for an *aribitrary* x (of type A), P x is satisfied. *)
  (* exists x : A, P x. Satisfied if there is some *specific* a such that P a is satisfied. *)


  (* Obviously, we can state specifications about infinite types as well: *)

  Check (forall l : week_day_list, l = [] \/ exists (w : week_day) (l' : week_day_list), l = Cons w l').

  (* Some of these specifications are satisfied, some are not. *)

  (* We give some basic tools to prove some of these specs: *)



  Lemma test1 : forall x y : week_day, x = y -> x = y.
  Proof.
    (* We now have a proof obligation! *)
    (* This puts us in proof mode, where instead of commands, *tactics* are expected. *)
    (* These use a different language, called Ltac. *)

    (* To prove a forall, you give generic names to the variables,
       and prove the goal for these generic variables.
       This is called *introducing* the variables.
     *)
    intros x y.
    (* To prove an implication, we can also use intros, but this time
       we are introducing a hypothesis, which we call H: *)
    intros H.
    (* Now we can use H to prove the goal, using apply *)
    apply H.
    (* We are done, there are no more goals! We use Qed to mark the end of a proof *)
  Qed.

  Print test1.

  (* We can check that test1 is indeed a proof of our specification by using the Check command *)
  Check test1.

  (* ---------------------------------------------------------
     There are some simple cheats on how to prove various kinds of specifications:
     roughly, one can try certain tactics based on the *shape* of the goal and the
     hypotheses. The breakdown is like this:

     | formula shape |   in goal   |   in hypotheses   |
     |---------------+-------------+------------------ |
     | A -> B        |  intros     |      apply        |
     | A /\ B        |  split      |     destruct      |
     | A \/ B        |  left/right |     destruct      |
     | ~A            |  intro      |      apply        |
     |  True         |  trivial    |       N/A         |
     |  False        |    N/A      |   contradiction   |
     | forall x, P x |  intros     |      apply        |
     | exists x, P x |  exists t   |     destruct      |
     | t = u         | reflexivity | rewrite/inversion |

     but of course, these will not alway suffice in all situations.
   *)


  (* Here's how one proves trivial equalities: *)
  Lemma test2 : Monday = Monday.
  Proof.
    reflexivity.
  Qed.

  (* It's nice to know that this doesn't always work: *)
  Lemma test2_fail : Monday = Friday.
  Proof.
    Fail reflexivity.
  Abort.

  Print return_monday.

  (* We can also perform computation steps in proofs, in order to
     prove things about functions: *)
  Lemma test3 : return_monday Friday = Monday.
  Proof.
    compute.
    reflexivity.
  Qed.

  Lemma test3' : length work_week = 5.
  Proof.
    compute.
    reflexivity.
  Qed.

  (* But really we're interested in behavior over *all inputs*. *)
  Lemma test4 : forall x : week_day, return_monday x = Monday.
  Proof.
    intros x.
    (* This works on symbolic inputs as well! *)
    compute.
    reflexivity.
  Qed.

  (* How about this? *)
  Lemma test5 : forall x : week_day, x == x = true.
  Proof.
    intros x.
    (* compute. *) (* uh oh *)
    (* We need to reason by cases over x. *)
    (* The tactic to do this is "destruct" *)
    destruct x.
    (* We end up with a bunch of cases,
       which we can *focus*, by using a dash.
       we handle each case with the usual technique. *)
    - compute.
      reflexivity.
    (* We are done with this dash, so we can move to the next one... *)
    - compute.
      reflexivity.
    - compute.
      reflexivity.
      (* ugh this is kind of boring *)
    - compute.
      reflexivity.
    - compute.
      reflexivity.
    - compute.
      reflexivity.
    - compute.
      reflexivity.
  Qed.

  (* Let's try again *)
  Lemma test5' : forall x : week_day, x == x = true.
  Proof.
    intros x.
    (* Because each case can be handled with the same tactic,
       we can apply it to each subgoal, using the ";" combinator. *)
    destruct x; compute; reflexivity.
  Qed.

  (* Let's play with some logical connectives *)

  (* We can declare variables of any type, including specification/predicates variables! *)
  Variables P Q R : Prop.

  Lemma test6 : P -> Q -> P /\ Q.
  Proof.
    intros H1 H2.
    (* This breaks a conjunction into 2 goals *)
    split.
    - apply H1.
    - apply H2.
  Qed.

  Lemma test7 : P -> P \/ Q.
  Proof.
    intros H.
    (* We need to pick a side! *)
    (* right. (* uh oh *) *)
    left.
    apply H.
  Qed.

  Lemma test8 : P /\ Q -> Q.
  Proof.
    intros H.
    (* Oh hey, destruct works here too! *)
    destruct H.
    apply H0.
  Qed.

  Lemma test9 : P \/ P -> P.
  Proof.
    intros H.
    (* Here destruct creates 2 subgoals, depending on which disjunct is true *)
    destruct H.
    - apply H.
    - apply H.
  Qed.

  (* A little less trivial *)
  Lemma test9' : P \/ Q -> Q \/ P.
  Proof.
    intros H.
    destruct H.
    - right; apply H.
    - left; apply H.
  Qed.

  (* And a classic! *)
  Lemma test9'' : (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R).
  Proof.
    intros H.
    destruct H.
    - destruct H.
      split.
      + left; apply H.
      + left; apply H0.
    - split; right; apply H.
  Qed.

  (* Let's do some more interesting things with equality: *)
  Lemma test10 : forall x y : week_day, x = Monday -> y = x -> y = Monday.
  Proof.
    intros x y H1 H2.
    (* Rewrite replaces the lhs of an equality by its rhs *)
    rewrite H2.
    rewrite H1.
    reflexivity.
  Qed.

  (* We can also rewrite *inside* hypotheses *)
  Lemma test10' : forall x y : week_day, x = Monday -> y = x -> y = Monday.
  Proof.
    intros x y H1 H2.
    rewrite H1 in H2.
    apply H2.
  Qed.

  (* Oh and we can rewrite backwards as well *)
  Lemma test10'' : forall x y : week_day, x = Monday -> y = x -> y = Monday.
  Proof.
    intros x y H1 H2.
    rewrite <- H2 in H1.
    apply H1.
  Qed.

  (* More proofs involving equalities *)
  Lemma test11 : Monday = Tuesday -> False.
  Proof.
    intro H.
    (* This tactic is very powerful, but for now,
       suffice to say that it can get contradictions from
       C1 = C2 where C1 and C2 are constructors *)
    inversion H.
  Qed.

  (* All right we're ready for some serious stuff *)
  Lemma first_real_lemma : forall x y : week_day, x = y -> x == y = true.
  Proof.
    intros x y.
    intros H.
    rewrite H.
    (* We can just apply our Lemma test5 here! *)
    apply test5.
  Qed.


  Locate "==".

  Check eq_wd.
  Print eq_wd.

  (* The other direction is harder! *)
  Lemma second_real_lemma : forall x y : week_day, x == y = true -> x = y.
  Proof.
    intros x y.
    intro H.
    (* destruct x. *)
    (* - destruct y. *)
    (*   + reflexivity. *)
    (*   + (* We can compute *in* hypotheses! *) *)
    (*     compute in H. *)
    (*     inversion H. *)
    (*     (* ugh. *) *)

    (* This fails *)
    (* destruct x; destruct y; reflexivity. *)

    (* This doesn't fail, but it leaves some goals unsolved. *)
    (* destruct x; destruct y; inversion H. *)

    (* We can use the "try", which *never* fails, but may leave some goals unchanged! *)
    destruct x; destruct y; try reflexivity; compute in H; congruence.
    (* Cool! *)
  Qed.


  Goal forall x y : week_day, x <> y -> x == y = false.
  Proof.
    intros.
    case_eq (x == y); intros.
    - contradict H.
      apply second_real_lemma.
      apply H0.
    - reflexivity.
  Qed.


  (* Now we have a program which we have proven correct! We can use this to prove some theorems! *)
  Lemma test12 : Monday = Monday.
  Proof.
    apply second_real_lemma.
    compute.
    reflexivity.
    (* Ok not overwhelming, but we can use this idea to prove harder things! *)
  Qed.


  (* Let's show correctness of our membership function! But first we need to *specify* membership. *)
  (* To do this, we specify an *inductive predicate*, which describes all the ways an element can be in a list. *)
  (* We can again use the keyword inductive. *)
  Inductive Mem : week_day -> week_day_list -> Prop :=
  | Mem_head : forall (w : week_day) (l : week_day_list), Mem w (Cons w l)
  | Mem_tail : forall (w w' : week_day) (l : week_day_list), Mem w l -> Mem w (Cons w' l).


  (* We can apply constructors of mem like lemmas *)
  Lemma test13 : Mem Tuesday [Monday; Tuesday; Thursday].
  Proof.
    apply Mem_tail.
    apply Mem_head.
  Qed.

  (* This one is significantly harder. We'll handle it later! *)
  Lemma test13' : forall (w : week_day), Mem w [Monday; Tuesday] -> w = Monday \/ w = Tuesday.
  Proof.
  Abort.

  Lemma test14 : exists w : week_day, Mem w work_week.
  Proof.
    exists Monday.
    (* Wait, we can't see the inside of work week! *)
    unfold work_week.
    (* Ok this works *)
    apply Mem_head.
  Qed.

  (* This is harder as well. We'll be able to prove this easily once we have the
     theorems.
   *)
  Lemma test15 : exists w : week_day, ~ (Mem w work_week).
  Proof.
  Abort.

  (* The theorems we want are these: *)
  Theorem is_a_member_correct : forall (w : week_day) (l : week_day_list),
      is_a_member w l = true -> Mem w l.
  Proof.
  Abort.

  Theorem is_a_member_complete : forall (w : week_day) (l : week_day_list),
      Mem w l -> is_a_member w l = true.
  Proof.
  Abort.


  Goal forall w, Mem w [Wednesday; Monday; Tuesday] -> Mem w work_week.
  Proof.
    unfold work_week.
  Abort.

  (*

    It might seem strange to specify the relatively simple is_a_member
    function in terms of the almost-as-complicated Mem predicate.

    HOWEVER, in real applications (e.g. CompCert) the specification is
    *vastly* simpler than the implementation. In addition we are then
    able to increasingly complicate the implementation, say by adding
    more efficiencies, but the specification should stay the same.

    It might even be a good idea to prove the simple implementation
    first, as a kind of "co-validation" of the spec and program. Then
    when we move to more complicated implementations, we can trust the
    specification more.

 *)


  (*
    To carry out these proofs, we need 2 addional tactics:
    - simpl, which is a special version of compute
    - induction, which is how we prove things about infinite types
   *)

  (* The simpl tactic evaluates a program, but keeps in in a more compact form, unfolding only when needed: *)
  Eval compute in is_a_member.
  Eval simpl in is_a_member.
  Eval compute in fun w l => is_a_member w (Cons Monday l).
  Eval simpl in fun w l => is_a_member w (Cons Monday l).

  (* Let's assume this for now (though it's not hard to prove with the right tools) *)
  Lemma n_leq_n_plus_1 : forall n m : nat, n < m -> n + 1 < m + 1.
  Proof.
  Admitted.

  (* And let's assume this as well: *)
  Lemma zero_leq_1 : 0 < 1.
  Proof.
  Admitted.

  (* induction: like it says on the tin! *)
  Lemma cons_len_gt : forall (w : week_day) (l : week_day_list),
      length l < length (Cons w l).
  Proof.
    simpl.
    intros w l.
    induction l.
    - simpl.
      apply zero_leq_1.
    - simpl.
      apply n_leq_n_plus_1.
      apply IHl.
  Qed.


Lemma eq_cases : forall x y, (x == y = true) \/ (x == y = false).
Proof.
  intros x y.
  destruct (x == y).
  - left; reflexivity.
  - right; reflexivity.
Qed.

  (* Now we're ready for the proofs! *)

  Theorem is_a_member_correct : forall (w : week_day) (l : week_day_list),
      is_a_member w l = true -> Mem w l.
  Proof.
    intros w l.
    induction l.
    - compute.
      intro H; inversion H.
    - simpl.
      assert (H := eq_cases w w0).
      destruct H.
      + intro H0.
         assert (w = w0) by (apply second_real_lemma; exact H).
         rewrite H1.
         apply Mem_head.
      + rewrite H.
         intro H1.
         apply Mem_tail.
         apply IHl.
         apply H1.
  Qed.

  Theorem is_a_member_complete : forall (w : week_day) (l : week_day_list),
      Mem w l -> is_a_member w l = true.
  Proof.
    intros w l H; induction H.
    - simpl.
      rewrite test5.
      simpl.
      reflexivity.
    - simpl.
      rewrite IHMem.
      destruct (w == w'); reflexivity.
  Qed.

  (* Let's try to prove the hard lemmas now: *)

  Lemma test13' : forall (w : week_day), Mem w [Monday; Tuesday] -> w = Monday \/ w = Tuesday.
  Proof.
    intros w H.
    assert (is_a_member w [Monday; Tuesday] = true).
    - apply is_a_member_complete; apply H.
    - revert H0.
      destruct w; compute; intros H1; try inversion H1.
      (* Nice! *)
      + left; reflexivity.
      + right; reflexivity.
  Qed.


  Lemma test15 : exists w : week_day, ~ (Mem w work_week).
  Proof.
    exists Sunday.
    intro H.
    assert (is_a_member Sunday work_week = true).
    - apply is_a_member_complete; apply H.
    - compute in H0.
      inversion H0.
      (* Easy peezy! *)
  Qed.

End Basics.
