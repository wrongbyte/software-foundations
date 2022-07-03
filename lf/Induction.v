From LF Require Export Basics.

Theorem add_0_l_firsttry: forall n:nat,
  0 + n = n.
Proof. simpl. reflexivity. Qed.
(** it can be done simply with reflexivity.**)


Theorem add_0_r_firsttry: forall n:nat,
  n + 0 = n.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - simpl. Abort.
(** If we try to use reflexivity
above, we get Unable to unify "S n" with "S (n + 0)" 
because S n is a inductive type, we would need to
destruct it again. **)

(** Given a proposition P, we need to:
  1 - show that P(O) holds; 
  2 - show that, for any n', if P(n') holds, then so does P(S n'); 
  conclude that P(n) holds for all n. 
**)

Theorem add_0_r : forall n: nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn']. (*n: the arbitrary natural number, IHn': the inductive hypothesis.*)
  - reflexivity.
  - simpl.
    rewrite IHn'. reflexivity. Qed.

(**
  the inductive tactics here replaces n' + 0 = n' by S n' + 0 = S n',
  what is: we are effectively applying the second criteria we defined
  from the principle of Induction.
**)

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - rewrite <- IHn'. simpl. reflexivity. Qed.

(** Exercise 1 - basic induction, 2 stars **)
Theorem mul_0_r: forall n: nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. rewrite <- IHn'. 
    reflexivity.
  Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - rewrite add_0_r. reflexivity.
  - simpl. 
    rewrite <- plus_n_Sm. 
    rewrite IHn'. 
    reflexivity.
  Qed.
    
Theorem add_assoc : forall n m p: nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.

(** Exercise 2 - double plus, 2 stars**)

Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


(** Use induction to prove this fact **)
Lemma double_plus: forall n, double n = n + n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
  Qed.


(**
Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.
**)

(** Optional exercise - using induction to prove a lemma about even function **)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite IHn'. 
    rewrite negb_involutive. 
    simpl. reflexivity.
Qed.

(** Differences destruct and induction **)

(**
  
  TL;DR Their main difference is the subgoal hypothesis.  
  
  The destruct tactic gives us a subgoal for each constructor of 
  an inductive type. It means that we have to prove that a proposition
  holds for both O or S n' for a nat type, for example.
  This creates as many goals as there are constructors in type T.
  
  On the other hand, induction generates subgoals as many as 
  there are constructors, and adds the inductive hypotheses in 
  the contexts. 
  
**)

(* ################################################################# *)
(** * Proofs Within Proofs *)
(** Assert is a way to create a quick proof
  about some statement, that is used in the goal
  we are trying to prove. 

  Assert generates:
  1 - A subgoal where we must prove the asserted fact
  2 - A second subgoal where we can use the asserted 
  fact to make progress on whatever we were trying to 
  prove in the first place. 
**)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

(** To use [add_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the _particular_ [m]
    and [n] that we are talking about here), prove this lemma using
    [add_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.


(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(* TODO *)


(* ################################################################# *)
(** * More Exercises *)

(** In the theorem below, assert helps us
  to change the order of elements; after 
  the two rewrites, we get n + m + p = m + n + p
  what is, we only need to change the positions
  of m and n, so assert does it for us here.
  Basically we use the same hypothesis defined
  previously, but we are kind of telling
  Coq how to replace stuff properly.**)

Theorem add_shuffle3: forall n m p: nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.  
  rewrite add_assoc. 
  rewrite add_assoc. 
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.


(** Commutativity of multiplication **)

(**
  Before proving the commutativity of multiplication, we have
  to prove that the multiplication distributes over addition.
**)

Theorem mul_dist: forall n m: nat,
  n * (S m) = n + n * m.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. 
    rewrite add_shuffle3. 
    reflexivity.
  Qed.


Theorem mul_comm: forall n m: nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - simpl. rewrite mul_0_r. reflexivity.
  - simpl. 
    rewrite IHn'.
    rewrite mul_dist. 
    reflexivity.
    Qed.

(** 
  The goal for the exercises below is to 
  think about the necessity for the use of
  simplification and rewriting, case analysis
  (destruct) or if it also requires induction.
 **)

Check leb.

(** Requires induction bc is an arbitrary number **)
Theorem leb_refl: forall n: nat,
  (n <=? n) = true.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.

