
Require Import Arith Bool.

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
  Definition add_one (x : nat) := x + 1.
  Definition return_monday (w : week_day) := Monday.

  Check add_one.
  Check return_monday.

  (* We can work by cases over sum types. *)
  Definition is_monday (w : week_day) :=
    match w with
    | Monday => true
    | _ => false
    end.

  Check is_monday.

  Eval compute in (is_monday Tuesday).

  (* There is a powerful search feature, which takes types and returns
     potentially useful functions with similar types *)
  SearchAbout (bool -> bool).

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

  (* How about a length function? This requires a special syntax: *)
  Fixpoint length (l : week_day_list) : nat :=
    match l with
    | [] => 0
    | Cons w ws => (length ws) + 1
    end.

  Eval compute in (length work_week).

  (* Now let's define a membership function *)
  Fixpoint is_a_member (w : week_day) (l : week_day_list) : bool :=
  (* ??? *)false.

  (* Let's test it: *)
  Eval compute in (is_a_member Monday work_week).
  Eval compute in (is_a_member Sunday work_week).

  (* Ok, we're ready for some specifications! *)
  (* The simplest kind of specification is equality: *)
  Check (Monday = Monday).

  (* The Prop type is the type of *specifications*. It is *not* bool! *)
  Check (forall w, w = Monday).
  Check (exists w, w = Monday).

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

  Check (forall l : week_day_list, l = [] \/ exists w l', l = Cons w l').

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

  (* We can check that test1 is indeed a proof of our specification by using the Check command *)
  Check test1.

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
  Lemma test5 : forall x : week_day, eq_wd x x = true.
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
  Lemma test5' : forall x : week_day, eq_wd x x = true.
  Proof.
    intros x.
    (* Because each case can be handled with the same tactic,
       we can apply it to each subgoal, using the ";" combinator. *)    
    destruct x; compute; reflexivity.
  Qed.

  (* Let's play with some logical connectives *)
  Lemma test6 : forall x y z : week_day, x = y -> y = z -> x = y /\ y = z.
  Proof.
    intros x y z.
    intros H1 H2.
    (* This breaks a conjunction into 2 goals *)
    split.
    - apply H1.
    - apply H2.
  Qed.

  Lemma test7 : forall x y z : week_day, x = y -> x = y \/ y = z.
  Proof.
    intros x y z H.
    (* We need to pick a side! *)
    (* right. (* uh oh *) *)
    left.
    apply H.
  Qed.

  Lemma test8 : forall x y z : week_day, x = y /\ y = z -> y = z.
  Proof.
    intros x y z H.
    (* Oh hey, destruct works here too! *)
    destruct H.
    apply H0.
  Qed.

  Lemma test9 : forall x y : week_day, x = y \/ x = y -> x = y.
  Proof.
    intros x y H.
    (* Here destruct creates 2 subgoals, depending on which disjunct is true *)
    destruct H.
    - apply H.
    - apply H.
  Qed.