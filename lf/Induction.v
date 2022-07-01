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

(** Exercise 1, 2 stars **)
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
    

