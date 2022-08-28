(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

(** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one (as with [nybble], and here): *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(** This declaration can be read: "The one and only way to
    construct a pair of numbers is by applying the constructor [pair]
    to two arguments of type [nat]." *)

Check (pair 3 5) : natprod.

(** Here are simple functions for extracting the first and
    second components of a pair. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Since pairs will be used heavily in what follows, it is nice
    to be able to write them with the standard mathematical notation
    [(x,y)] instead of [pair x y].  We can tell Coq to allow this with
    a [Notation] declaration. *)

Notation "( x , y )" := (pair x y).

(** The new notation can be used both in expressions and in pattern
    matches. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Note that pattern-matching on a pair (with parentheses: [(x, y)])
    is not to be confused with the "multiple pattern" syntax (with no
    parentheses: [x, y]) that we have seen previously.  The above
    examples illustrate pattern matching on a pair with elements [x]
    and [y], whereas, for example, the definition of [minus] in
    [Basics] performs pattern matching on the values [n] and [m]:

       Fixpoint minus (n m : nat) : nat :=
         match n, m with
         | O   , _    => O
         | S _ , O    => n
         | S n', S m' => minus n' m'
         end.

    The distinction is minor, but it is worth knowing that they
    are not the same. For instance, the following definitions are
    ill-formed:

        (* Can't match on a pair with multiple patterns: *)
        Definition bad_fst (p : natprod) : nat :=
          match p with
          | x, y => x
          end.

        (* Can't match on multiple values with pair patterns: *)
        Definition bad_minus (n m : nat) : nat :=
          match n, m with
          | (O   , _   ) => O
          | (S _ , O   ) => n
          | (S n', S m') => bad_minus n' m'
          end.
*)

(** Now let's try to prove a few simple facts about pairs.

    If we state properties of pairs in a slightly peculiar way, we can
    sometimes complete their proofs with just reflexivity (and its
    built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

(** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** Instead, we need to expose the structure of [p] so that
    [simpl] can perform the pattern match in [fst] and [snd].  We can
    do this with [destruct]. *)

(** 
  We first need to destruct the elements within
  p to use them in the pattern matching that
  happens both in fst and snd. Try to substitute 
  simpl by unfold fst in the theorem above and below
  to see how it works.
**)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(** Notice that, unlike its behavior with [nat]s, where it
    generates two subgoals, [destruct] generates just one subgoal
    here.  That's because [natprod]s can only be constructed in one
    way. *)

(** **** Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl.
  reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl.
  reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Lists of Numbers *)

(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

Inductive natlist: Type := 
  | nil
  | cons (n: nat) (l: natlist).

(* Three-element list *)
Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(* Defining a more familiar notation for lists *)
Notation "x :: l" := (cons x l)
  (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(**
  Examples:
  [1;2] = (cons x (cons y nil)). -> (cons 1 (cons 2 nil)).
  [1;2;3] = (cons x (cons y (cons z nil))) -> (cons 1 (cons 2 (cons 3 nil))).
**)
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].


(**
The second and third Notation declarations above introduce 
the standard square-bracket notation for lists; the right-hand side
 of the third one illustrates Coq's syntax for declaring n-ary 
 notations and translating them to nested sequences of binary 
 constructors. 
**)

(* Functions for constructing and manipulating lists *)

(* repeats a number n count times *)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* calculates the length of a list *)
Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* concatenates two lists *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
(right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(* Head and Tail *)
Definition hd (default : nat) (l: natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l: natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* Exercises *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => (nonzeros t)
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
           match even h with
           | true => (oddmembers t)
           | false => h :: (oddmembers t)
           end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  unfold countoddmembers. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  simpl. reflexivity. Qed.
(** [] *)

(** Advanced exercises - alternate **)
(**

Complete the following definition of alternate, which interleaves two lists into one, alternating between elements taken from the first list and elements from the second. See the tests below for more specific examples.
(Note: one natural and elegant way of writing alternate will fail to satisfy Coq's requirement that all Fixpoint definitions be "obviously terminating." If you find yourself in this rut, look for a slightly more verbose solution that considers elements of both lists at the same time. One possible solution involves defining a new kind of pairs, but this is not the only way.) 

**)

(** here we will have to use the multiple pattern syntax
**)
Fixpoint alternate (l1 l2 : natlist) :natlist :=
match l1, l2 with 
  | [], [] => nil
  | l1, [] => l1
  | [], l2 => l2
  | h1::t1, h2::t2 => h1 :: h2 :: (alternate t1 t2)
  end. 


Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  simpl. reflexivity. Qed.

Example test_alternate2: 
  alternate [1] [4;5;6] = [1;4;5;6].
  simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  simpl. reflexivity. Qed.

(* Bags via Lists *)

(**

A bag (or multiset) is like a set, except that each element can appear multiple times rather than just once. One possible representation for a bag of numbers is as a list. 

**)
Definition bag := natlist.

(* Bag functions *)
(*  Complete the following definitions for the functions count, sum, add, and member for bags. *)
(* why doesn't work with match v with h? *)
Fixpoint count (v: nat) (s: bag) : nat :=
  match s with
  | nil => O
  | h :: t => match eqb h v with
            | true => S (count v t)
            | false => count v t
            end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 reflexivity. Qed.


Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v: nat) (s: bag) : bag :=  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  negb (eqb (count v s) 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
(* simpl does nothing above *)

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match eqb h v with
            | true => t
            | false => h :: (remove_one v t)
            end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.



Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match eqb h v with
            | true => remove_all v t
            | false => h :: (remove_all v t)
            end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1: bag) (s2: bag) : bool :=
  match s1 with
  | nil => true
  | h1 :: t1 => match member h1 s2 with
              | false => false
              | true => included t1 (remove_one h1 s2)
              end
  end.


Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* if we get to the nil, it is because we've "consumed" all elements
 and as they're contained in the set, it is the true case *)
Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | h1::t1 => member h1 s2 && subset t1 (remove_one h1 s2)
  end.


Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* Adding a value to a bag should increase the value's count by one. State that as a theorem and prove it. *)

Theorem bag_theorem : forall (n: nat) (s: bag),
  count n (add n s) = S (count n s).
Proof.
intros n s.
simpl.
rewrite eqb_refl.
reflexivity. Qed.

(* Reasoning about lists *)

 Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

(* Notice that the as annotation on the destruct tactic here introduces two names, n and l', corresponding to the fact that the cons constructor for lists takes two arguments (the head and tail of the list it is constructing).
 *)


Theorem app_assoc: forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| h1 t1 IHl1']. 
  - simpl. reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
  Qed.

(* Reversing a list *)

Fixpoint rev (l: natlist): natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h] (* a list with h nil *)
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(* Proving that reversing a list does
  not change its length *)

Theorem rev_length_firsttry: forall l : natlist, 
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. Abort.
(* we get stuck at
length (rev l' ++ [n]) = S (length (rev l'))
But we can make an equation to help us to make
progress.
*)

(*
  we must simplify the length (rev l' ++ [n]) part,
  making it equivalent to S (length (rev l')) in terms
  of its "structure". we are basically adding the
  length of two lists, and the result of this operation
  must be a nat number, which then can be compared to
  S (length [...]). To state this lemma, we can
  use induction on lists.
*)
Theorem app_length: forall l1 l2: natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHl1].
  - reflexivity.
  - (* length ((h1 :: t1) ++ l2) = length (h1 :: t1) + length l2 *)
  simpl. rewrite IHl1. reflexivity.
  Qed.


(* todo: make notes about it.*)
Theorem rev_length : forall l: natlist,
  length (rev l) = length l.
Proof.
  intros l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite app_length.
    simpl. rewrite IHl. rewrite add_comm.
    simpl. reflexivity. Qed. 


Search (_ + _ = _ + _) inside Induction.


Theorem app_nil_r: forall l: natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2: natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHl1].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc.
    reflexivity. Qed.

Theorem rev_involutive: forall l: natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl.
    rewrite IHl. reflexivity.
Qed.

Theorem app_assoc4: forall l1 l2 l3 l4: natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc. rewrite app_assoc.
  reflexivity. Qed.


Lemma nonzeros_app: forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 IHl1].
  - simpl. reflexivity.
  - destruct h1.
    + simpl. rewrite IHl1. reflexivity.
    + simpl. rewrite IHl1. reflexivity.
  Qed.


Fixpoint eqblist (l1 l2: natlist): bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => (eqb h1 h2) && (eqblist t1 t2)
  | _, _ => false
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
  simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
  simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
  simpl. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl.
    rewrite eqb_refl. rewrite <- IHl.
    simpl. reflexivity.
Qed.


Theorem count_member_nonzero : forall (s: bag),
  1 <=? (count 1 (1::s)) = true.
Proof.
  intros s.
  induction s as [| h t ].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count:
  forall (s: bag), (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s as [| h t IHs].
  - simpl. reflexivity.
  - destruct h as [| n'].
    + simpl. rewrite leb_n_Sn. reflexivity.
    + simpl. rewrite IHs. reflexivity.
Qed.

(* Proof that every involution is injective *)
(* An injective function is one-to-one: 
  it maps distinct inputs to distinct outputs, 
  without any collisions.  *)
Theorem involution_injective : forall (f : nat -> nat),
  (forall n : nat, n = f (f n)) ->
  (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f hyp_involutive_f n1 n2 n1_eq_n2.
  rewrite hyp_involutive_f.
  rewrite <- n1_eq_n2.
  rewrite <- hyp_involutive_f.
  reflexivity.
Qed.

(* Proof that rev is injective *)
Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 revl1_eq_revl2.
  rewrite <- rev_involutive.
  rewrite <- revl1_eq_revl2.
  rewrite rev_involutive.
  reflexivity.
Qed.

(* Options *)
(*function that returns the nth element of some list*)

(* as we have nat as the return type, we must return a 
  number even if we are passing an empty list to this
  function. however, the list may not have enough
  elements and therefore, we would have to
  return an arbitrary number. *)
Fixpoint nth_bad (l: natlist) (n: nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
              | 0 => a
              | S n' => nth_bad l' n'
              end
  end.

Inductive natoption : Type :=
  | Some (n: nat)
  | None.

Fixpoint nth_error (l: natlist) (n: nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
              | 0 => Some a
              | S n' => nth_error l' n'
              end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.


Definition option_elim (d: nat) (o: natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(*
* Definition hd (default : nat) (l : natlist) : nat :=
*  match l with
*  | nil ⇒ default
*  | h :: t ⇒ h
*  end.
*)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd: forall (l: natlist) (default: nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  induction l as [| h t IHl'].
  - reflexivity.
  - reflexivity.
Qed.




