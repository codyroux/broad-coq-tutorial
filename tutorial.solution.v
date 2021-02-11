(* Copy and paste this whole file into https://x80.org/collacoq/ *)
From Coq Require Import Arith Bool.

(* At its core, Coq is a *typed* programing language *)
(* There are a few (not many!) built-in types *)
(*

   On the online version, you can move your cursor up and down with
   Alt+p and Alt+n respectively.

   The result of the command should show up in the lower right hand
   side of the screen.

   Remember to leave it time to load up at the very beginning!

 *)
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

(* Not to be confused with the *top level command* "Print", which asks
the Coq *system* to print a definition. *)
Print bool.

(*

  NB: Every piece of data in a program is *constant* and *immutable*
  There are good reasons for this, which we will go into later.

 *)

(* We can define types. This is a simple sum type *)
Inductive week_day :=
| Monday : week_day
| Tuesday : week_day
| Wednesday : week_day
| Thursday : week_day
| Friday : week_day
| Saturday : week_day
| Sunday : week_day.

Check Thursday.

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
(* WARNING: this does not work on the online version! *)
(* Search (bool -> bool). *)

(* We can define types which may be recursive, e.g. the type of lists *)
Inductive week_day_list :=
| Nil : week_day_list
| Cons : week_day -> week_day_list -> week_day_list.

Check (Cons Monday (Cons Tuesday Nil)).

(* Ok, we have lisp-style lists. Can we define head? *)
Definition head (l : week_day_list) (default : week_day) : week_day :=
  match l with
  | Nil => default
  | Cons w _ => w
  end.
(* We need a default value! A little unfortunate... but the price of being pure! *)

(* How about tail? *)
Definition tail (l : week_day_list) : week_day_list :=
  match l with
  | Nil => Nil
  | Cons _ l' => l'
  end.

(* List notation a la lisp is tedious. Thankfully, Coq's notation system is incredibly powerful! *)

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
  match l with
  | [] => false
  | Cons w' ws => eq_wd w w' || is_a_member w ws
  end.

(* Let's test it: *)
Eval compute in (is_a_member Monday work_week).
Eval compute in (is_a_member Sunday work_week).

(* Ok, we're ready for some specifications! *)
(* The simplest kind of specification is equality: *)
Check (Monday = Monday).

(* The Prop type is the type of *specifications*. It is *not* bool! *)
Check (forall w, w = Monday).
Check (exists w, w = Monday).

(* The basic propositional connectives: *)
(* True. Always provable. *)
(* False. Never provable. *)
(* P\/Q. Provable if one of P or Q (or both) is provable. *)
(* P/\Q. Provable if both P and Q are provable. *)
(* P -> Q. Provable if, when *assuming* P is provable, then so is Q. *)
(* ~P. Provable if P is *never* provable *)
(* forall x : A, P x. Provable if for an *arbitrary* x (of type A), P x is provable. *)
(* exists x : A, P x. Provable if there is some *specific* a such that P a is provable. *)
(* a = b. Provable if, in fact, a is equal to b. Not to be confused
   with ":=" which is how we define functions and constants (and is
   *not* a connective).  *)


(* Obviously, we can state specifications about infinite types as well: *)

Check (forall l : week_day_list, l = [] \/ exists w l', l = Cons w l').

(* Some of these specifications are provable, some are not. *)

(* We give some basic tools to prove some of these specs: *)



Lemma test1 : forall x y : week_day, x = y -> x = y.
Proof.
  intros x y h.
  apply h.
Qed.


(* ---------------------------------------------------------
     There are some simple cheats on how to prove various kinds of specifications:
     roughly, one can try certain tactics based on the *shape* of the goal and the
     hypotheses. The breakdown is like this:

     |               |   in goal   |   in hypotheses   |
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

     but of course, these will not always suffice in all situations.
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
  compute.
  reflexivity.
Qed.

(* How about this? Hint: use the [case some_variable] tactic *)
Lemma test5 : forall x : week_day, eq_wd x x = true.
Proof.
  intros x.
  case x; compute; reflexivity.
Qed.

(* Let's play with some logical connectives *)
Lemma test6 : forall x y z : week_day, x = y -> y = z -> x = y /\ y = z.
Proof.
  intros x y z h1 h2.
  split.
  - apply h1.
  - apply h2.
Qed.

Lemma test7 : forall x y z : week_day, x = y -> x = y \/ y = z.
Proof.
  intros x y z h.
  left.
  apply h.
Qed.

Lemma test8 : forall x y z : week_day, x = y /\ y = z -> y = z.
Proof.
  intros x y z h.
  destruct h as [h1 h2].
  apply h2.
Qed.

(* This one is a little tougher! tactic order matters! *)
Lemma test9 : forall x y z : week_day, x = y \/ x = z -> x = z \/ x = y.
Proof.
  intros x y z h.
  destruct h as [h | h].
  - right. apply h.
  - left. apply h.
Qed.

(* Proofs involving equalities *)
Lemma test10 : forall x y, x = Monday -> y = x -> y = Monday.
Proof.
  intros x y h1 h2.
  rewrite h2.
  apply h1.
Qed.

Lemma test11 : Monday = Tuesday -> False.
Proof.
  intros h.
  inversion h.
Qed.

(* All right we're ready for some serious stuff *)
Lemma first_real_lemma : forall x y, x = y -> eq_wd x y = true.
Proof.
  intros x y h.
  rewrite h.
  apply test5.
Qed.

(* The other direction is harder! *)
Lemma second_real_lemma : forall x y, eq_wd x y = true -> x = y.
Proof.
  intros x y h.
  destruct x; destruct y; trivial || unfold eq_wd in h; inversion h.
Qed.

(* Now we have a program which we have proven correct! We can use this to prove some theorems! *)
Lemma test12 : Monday = Monday.
Proof.
  apply second_real_lemma.
  compute.
  reflexivity.
Qed.

(* Let's show correctness of our membership function! But first we need to *specify* membership. *)
(* To do this, we specify an *inductive predicate*, which describes all the ways an element can be in a list. *)
(* We can again use the keyword inductive. *)
Inductive Mem : forall (w : week_day) (l : week_day_list), Prop :=
| Mem_head : forall w l, Mem w (Cons w l)
| Mem_tail : forall w w' l, Mem w l -> Mem w (Cons w' l).


(* We can apply constructors of Mem like lemmas *)
Lemma test13 : Mem Monday [Tuesday; Monday; Thursday].
Proof.
  (* here's a slick proof! *)
  (* repeat constructor. *)
  apply Mem_tail.
  apply Mem_head.
Qed.

(* Here's some fun existential statements: *)
Lemma test14 : exists w, Mem w work_week.
Proof.
  exists Monday; apply Mem_head.
Qed.

(* This is harder! We'll be able to prove this easily once we have the
     theorems.
 *)
Lemma test15 : exists w, ~ (Mem w work_week).
Proof.
Abort.

(* The theorems we want are these: *)
Theorem is_a_member_correct : forall w l, is_a_member w l = true -> Mem w l.
Proof.
  intros w l.
  induction l.
  - compute.
    intros h; inversion h.
  - (* [simpl] is usually better than [compute] in proofs. *)
    simpl.
    case_eq (eq_wd w w0); intro h.
    + assert (h1 : w = w0).
      -- apply second_real_lemma.
         apply h.
      -- intros _.
         rewrite h1.
         apply Mem_head.
    + simpl.
      intro h1.
      apply Mem_tail.
      apply IHl.
      apply h1.
Qed.

Theorem is_a_member_complete : forall w l, Mem w l -> is_a_member w l = true.
Proof.
  intros w l h.
  (* We can do induction on inductive predicates! *)
  induction h.
  - simpl.
    (* you can rewrite lemmas! *)
    rewrite first_real_lemma.
    + simpl; reflexivity.
    + reflexivity.
  - simpl.
    rewrite IHh.
    case (eq_wd w w'); simpl; reflexivity.
Qed.

Lemma test15 : exists w, ~ (Mem w work_week).
Proof.
  exists Sunday.
  intro h.
  assert (h1 : is_a_member Sunday work_week = true).
  - apply is_a_member_complete.
    apply h.
  - compute in h1.
    inversion h1.
Qed.

(*

  Finally, it's important to note that I purposefully hid a number of
  powerful tactics from you, for pedagogical reasons. The easiest of
  these is [auto], which tries to apply simple steps to finish a
  goal. Exercise: how much easier are the lemmas to prove using
  [auto]?

*)

(*

  There is still a lot to learn! You can check out the resources on
  https://coq.inria.fr/, most notably the tutorials on
  https://coq.inria.fr/documentation.

  You can try more online stuff on rhino-coq:
  https://x80.org/rhino-coq/

  I have a few things on my github:
  https://github.com/codyroux?tab=repositories&q=&type=&language=coq

  Or create an account on https://coq.zulipchat.com, and ask questions
  there!

  Go forth and prove!

 *)
