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
(* mumble is the "type argument"*)
Check d mumble (b a 5).

