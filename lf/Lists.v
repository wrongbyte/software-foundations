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
 reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
 reflexivity. Qed.




