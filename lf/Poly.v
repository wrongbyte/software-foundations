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

(* Polymorphic Pairs or products *)
Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y: Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

(* (x,y) is a value built from two other values, while
  x*y is a type built from two other types. *)


Definition fst {X Y : Type} (p: X * Y) : X :=
  match p with 
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* zip takes two lists and combine them
  into a list of pairs *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
    : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check combine.
Compute (combine [1;2] [false;false;true;true]).

(* split takes a list of pairs and returns a pair
  of lists. it is also called unzip *)

Fixpoint split {X Y : Type} (l: list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' => match (split l') with
                    | (x', y') => (x::x', y::y')
                    end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity. Qed.


(* Polymorphic Options *)
Module OptionPlayground.

Inductive option (X: Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) :=
  match l with
  | nil => None
  | a :: l' => match n with
              | O => Some a
              | S n' => nth_error l' n'
              end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(* Functions as Data *)
Definition doit3times {X : Type} (f: X->X) (n : X): X :=
  f (f (f n)).
(* applies f three times to some value n *)

 Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (7 <=? n) && even n) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed. 

Definition partition {X : Type}
                     (test: X -> bool)
                     (l : list X)
                   : list X * list X :=
(filter test l, filter (fun x => negb (test x)) l).
(* we create a pair with the resulting lists
  from applying filter with test to each element
  and from applying filter with the negb of test
  to each element of the list (using an anonymous
  function 
*)


Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Map *)
Fixpoint map {X Y : Type} (f: X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.


Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.


(* The element types of the input and output lists need not
   be the same, since map takes two type arguments, X and Y. 
*)

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

(*
  It can even be applied to a list of numbers and a 
  function from numbers to lists of booleans to yield
  a list of lists of booleans: 
*)

 Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* map and rev are commutative *)

(* Auxiliar theorem: distributive on map app *)

(* both have type X as this is the type of the input list. 
   we apply a function X->Y to each element of each list, so
   in the end we append two lists of type Y.*)
Theorem map_app_distr: forall (X Y : Type) (f: X -> Y) (l1 l2: list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h1 t1 IHl1].
    - reflexivity.
    - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f: X -> Y) (l: list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite <- IHl. rewrite map_app_distr.
    simpl. reflexivity.
Qed.   

(* flat_map: a map that uses a function of type X->list Y *)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y :=
  match l with 
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.


(* Fold *)
 Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* functions that construct functions *)

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k: nat) => x.

(* ftrue is built from constfun *)
Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus: nat -> nat -> nat.

(*
  The function "plus" by itself has three binary operators.
  As it is right-associative, it is the same as writing
  nat -> (nat -> nat).
  Plus is a one-argument function that takes nat and returns
  a one-argument function that takes another nat and returns
  a nat.
  
  Basically: one argument -> function (partial application)
  two arguments -> number 
*)

Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.


(* Additional exercises *)
Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.

(* fold applies a binary operator between every two elements of a list *)
(* the return of our anonymous function should be a list *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun h t => f h::t ) l [].


Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
  intros.
  induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.


(* Currying *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Check prod_curry.

(* To uncurry, we need to "destruct" the pair from
  p. *)
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
  | (x, y) => f x y
  end.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros.
  destruct p as [x y].
  reflexivity.
Qed.




