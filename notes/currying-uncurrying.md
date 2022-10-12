## Currying and uncurrying

If we take plus, for example, and check its type, we will see:
`Check plus : nat → nat → nat.`

We know that plus takes two arguments, so that we are able to sum two numbers. But actually, what happens here is that `plus` takes a nat **and** returns
another function if we don't provide the second argument. It can be rewritten as `nat → (nat → nat).`

>Each → in this expression is actually a binary operator on types. This operator is right-associative, so the type of plus is really a shorthand for nat → (nat → nat) -- i.e., it can be read as saying that "plus is a one-argument function that takes a nat and returns a one-argument function that takes another nat and returns a nat."

If we do so, we are doing what's called **partial application**. We can do it when we have functions that can return another functions when we don't provide all arguments to them.
By contrast, functions of type X × Y → Z -- which when fully parenthesized is written (X × Y) → Z -- require their single input to be a pair. Both arguments must be given at once; there is no possibility of partial application.
It is possible to convert a function between these two types. **Converting from X × Y → Z to X → Y → Z is called currying**, in honor of the logician Haskell Curry. **Converting from X → Y → Z to X × Y → Z is called uncurrying**. 

Let's see it in detail:
```coq
Definition prod_curry {X Y Z : Type}
  (f : X × Y → Z) (x : X) (y : Y) : Z := f (x, y).
```

In the definition above, we take a function that has a product (a pair) as its input. 

We also have its opposite, _uncurry_:
```coq
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
  | (x, y) => f x y
  end.
```
Note that, in order to return this function applied to both arguments of the product, we first need to destruct this product into two arguments.
Therefore, in both definitions, we are essentially doing the inverse: if we want to curry a function, we take its argument (that sould be a pair) and apply it as if each member of the pair was one entity.
While uncurrying, we do the opposite: we consider the two arguments received as a pair and apply the function to them.


### Proofs
```coq
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
```

The first case can be easily proved when reducing the functions, so that we only need `reflexivity`.
In the second proof, however, we get
```
p : X * Y
______________________________________(1/1)
prod_uncurry (prod_curry f) p = f p
```

as part of the goal. We need to use `destruct` in this case.
