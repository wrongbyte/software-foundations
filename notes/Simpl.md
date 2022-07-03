### What simpl does?
Let's say we have the following theorem:
```Coq
Theorem test : forall n: nat,
   S n + 0 = S (n + 0).
```
When writing the proof, the tactic `simpl.` produces:
```Coq
S (n + 0) = S (n + 0)
```
It is a function that computes your program. `simpl` computes the normal form of your expression; it kind of "unpack" definitions.
For example,
```Coq
(* From the Basics module. *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => mult n (factorial n')
  end. 

(*Simpl. computes the defined function. *)
Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity.  Qed.
```
However, what if we could see the steps `simpl` does under the hood? A way to do this is using `unfold`.
It then transforms `factorial 3` into `3 * (2 * (1 * 1)) = 6`
```Coq
(*Using unfold, we can see the resulting unpack *)
Example test_factorial_unfold:          (factorial 3) = 6.
Proof.
 unfold factorial. reflexivity.  Qed.
```

An important note is that, when we say that `simpl` "computes" your program, there is a main criteria for when a program can be "reduced" or "executed". It is only possible when Coq can resolve the conditionals - for example, `if b then 0 else 1` is an expression that cannot be reduced, because b is yet unknown. That's when case analysis or rewrite come into play.

Let's see an example, proving that negb is involutive:
```Coq
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. 
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.
```

We are using destruct to make a case analysis for each constructor of `bool` type. 
If we replace `destruct b eqn:E.` by `unfold negb.`, our goal would change from 
```Coq
negb (negb b) = b
```
to
```Coq
(if if b then false else true then false else true) = b
```
We then would get stuck at the problem of evaluating an expression with an unknown variable.
If we add the destruct line after the unfold, however, then we can now use reflexivity, because the goal would be replaced with the result of evaluating the `negb` function for each given value (the constructors of the inductive type `bool`).

![coqide](https://dev-to-uploads.s3.amazonaws.com/uploads/articles/144f9degdzxwo6m586i7.png)
