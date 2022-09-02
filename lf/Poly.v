From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(* polymorphic inductive type definitions *)
Inductive list (X: Type) : Type :=
  | nil
  | cons (x: X) (l : list X).

(*
  The definition of list is a function from Types to 
  Inductive definitions.
  A list is a function from Types to Types.
  For any particular type X, the type list X is the
  Inductively defined set of lists whose elements are
  of type X.
*)

Check list: Type -> Type.

(*
  The X is now a parameter for the constructors nil and cons,
  what means they are now polymorphic constructors. When we
  use them, we must provide a first argument that is the
  type of the list they are building. For example, nil nat
  constructs the empty list of type nat. 
*)

Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X: Type, X -> list X -> list X.

(* polymorphic version of the repeat function *)

Fixpoint repeat (X : Type) (x: X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* mumble grumble *)
Module MumbleGrumble.

(* mumble is a Set that contains a, b, or c*)
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

(* grumble is Type -> Type *)
Inductive grumble (X : Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)] NO, you have to add the type argument
      - [d mumble (b a 5)] YES
      - [d bool (b a 5)] YES (it returns grumble bool)
      - [e bool true] YES
      - [e mumble (b c 0)] YES
      - [e bool (b c 0)] NO, because the e constructor must have the 
                        same argument that is binded to X, but we are
                        using X = bool and b c 0 is of type mumble.
      - [c] YES *)


Check mumble.
Check grumble.

Check d bool (b a 5).
Check e mumble (b c 0).
Check c.
Check d (nat). (* mumble -> grumble nat *)
(* mumble is the type argument*)
Check d mumble (b a 5).

End MumbleGrumble.

(* Type annotation inference *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.




(*
 It has exactly the same type as repeat. Coq was able to use type inference to deduce what the types of X, x, and count must be, based on how they are used. For example, since X is used as an argument to cons, it must be a Type, since cons expects a Type as its first argument; matching count with 0 and S means it must be a nat; and so on.
This powerful facility means we don't always have to write explicit type annotations everywhere, although explicit type annotations can still be quite useful as documentation and sanity checks, so we will continue to use them much of the time.

*)

(* Type argument synthesis *)
(* similar to type annotation inference. we use "holes"
  totell Coq to attempt to infer the missing information.
*)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.


(* Implicit arguments *)
(* we can avoid writing _'s by telling Coq to always
  infer the type arguments of a given function. 
  The Arguments directive specifies the name of the
  function (or constructor) then lists the (leading)
  argument names to be treated as implicit, each
  surrounded by curly braces.
*)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(* now we dont' have to supply any type arguments *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(*Alternatively, we can declare an argument to be 
  implicit when defining the function itself, by 
  surrounding it in curly braces instead of parens.  *)


Fixpoint repeat''' {X : Type} (x: X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l: list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.


Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* Supplying type arguments explicitly *)

(* The example below fails because nil is a constructor
of Type list. However, even though list has implicit type
arguments, Coq has no info available to infer the type of nil below. *)
Fail Definition mynil := nil.


(* @ is used to force implicit arguments to be explicit*)

Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Exercises *)
Theorem app_nil_r : forall (X:Type), forall l: list X,
  l ++ [] = l.
Proof.
  intros T l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros T l m n.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma app_length : forall (X: Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros T l1 l2.
  induction l1 as [| h1 t1 IHl1].
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros T l1 l2.
  induction l1 as [| h1 t1 IHl1].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite app_assoc. rewrite IHl1. reflexivity.
Qed.


Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros T l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl.
    rewrite IHl. reflexivity.
Qed.

