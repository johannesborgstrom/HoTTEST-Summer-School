# Week 6 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module Pool.Homework.homework6 where

open import prelude
open import isomorphisms
open import natural-numbers-functions
open import Fin
open import Vector
```

## Part I: Isomorphisms

### Exercise 1.1

**Prove** the following isomorphism:

```agda
×-distributivity-+ : (X Y Z : Type) → (X ∔ Y) × Z ≅ (X × Z) ∔ (Y × Z)
×-distributivity-+ X Y Z ._≅_.bijection (inl x , z) = inl (x , z)
×-distributivity-+ X Y Z ._≅_.bijection (inr y , z) = inr (y , z)
×-distributivity-+ X Y Z ._≅_.bijectivity .is-bijection.inverse (inl (x , z)) = inl x , z
×-distributivity-+ X Y Z ._≅_.bijectivity .is-bijection.inverse (inr (y , z)) = inr y , z
×-distributivity-+ X Y Z ._≅_.bijectivity .is-bijection.η (inl x , z) = refl _
×-distributivity-+ X Y Z ._≅_.bijectivity .is-bijection.η (inr y , z) = refl _
×-distributivity-+ X Y Z ._≅_.bijectivity .is-bijection.ε (inl (x , z)) = refl _
×-distributivity-+ X Y Z ._≅_.bijectivity .is-bijection.ε (inr (y , z)) = refl _
```

### Exercise 1.2

We now define a function `alternate` that takes two types `X` and `Y` and
evaluates to `X` on `true` and evaluates to `Y` on `false`.

```agda
alternate : Type → Type → Bool → Type
alternate X _ true  = X
alternate _ Y false = Y
```

It can be proved that `Σ b ꞉ Bool , alternate X Y b` is the same thing as `X ∔
Y`. **Prove** this by constructing the following isomorphism:

```agda
∔-isomorphic-to-Σ-bool : (X Y : Type) → (X ∔ Y) ≅ (Σ b ꞉ Bool , alternate X Y b)
∔-isomorphic-to-Σ-bool X Y ._≅_.bijection (inl x) = true  , x
∔-isomorphic-to-Σ-bool X Y ._≅_.bijection (inr y) = false , y
∔-isomorphic-to-Σ-bool X Y ._≅_.bijectivity .is-bijection.inverse (true  , x) = inl x
∔-isomorphic-to-Σ-bool X Y ._≅_.bijectivity .is-bijection.inverse (false , y) = inr y
∔-isomorphic-to-Σ-bool X Y ._≅_.bijectivity .is-bijection.η (inl _) = refl _
∔-isomorphic-to-Σ-bool X Y ._≅_.bijectivity .is-bijection.η (inr _) = refl _
∔-isomorphic-to-Σ-bool X Y ._≅_.bijectivity .is-bijection.ε (true  , _) = refl _
∔-isomorphic-to-Σ-bool X Y ._≅_.bijectivity .is-bijection.ε (false , _) = refl _
```

## Part II: Proving correctness of efficient Fibonacci

In Functional Programming you saw two ways of defining the Fibonacci function.
The first one, `fib` was fairly simple, but inefficient

```agda
fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)
```

Therefore, we introduce a second version, `fib-fast`, which uses an accumulating
parameter to make it more efficient.

```agda
fib-aux : ℕ → ℕ → ℕ → ℕ
fib-aux a b 0       = b
fib-aux a b (suc n) = fib-aux (b + a) a n

fib-fast : ℕ → ℕ
fib-fast = fib-aux 1 0
```

It is not obvious, however, that `fib-fast` implements the same behaviour as
`fib`. In Agda, we can *prove* this, showing that `fib-fast` is correct.

The following lemma relates `fib-aux` and `fib` and is fundamental in proving
the correctness of `fib-fast`. You will be asked to prove it later.

```agda
fib-aux-fib-lemma : (k n : ℕ) → fib-aux (fib (suc n)) (fib n) k ≡ fib (k + n)
fib-aux-fib-lemma zero zero = refl _
fib-aux-fib-lemma zero (suc n) = refl _
fib-aux-fib-lemma (suc k) n =
                 fib-aux (fib (suc (suc n))) (fib (suc n)) k
                   ≡⟨ fib-aux-fib-lemma k (suc n) ⟩
                 fib (k + suc n)
                   ≡⟨ ap fib (+-step k n) ⟩
                 fib (suc k + n)
                   ∎
```

### Exercise 2.1

Using `fib-aux-fib-lemma`, **prove** the correctness of `fib-fast`.

```agda
fib-fast-is-correct : (n : ℕ) → fib-fast n ≡ fib n
fib-fast-is-correct n =
  fib-aux (fib 1) (fib 0) n
    ≡⟨ fib-aux-fib-lemma n 0 ⟩
  fib (n + 0)
    ≡⟨ ap fib (+-base n) ⟩
  fib n  
    ∎
```

*Hints*:
1. The lemma allows you to prove this fairly directly. There is no need to do
induction on `n`.
1. You may also find the `+-base` function from the
[natural-numbers-functions](../natural-numbers-functions.lagda.md) module useful.

### Exercise 2.2

Now **complete** the proof of fundamental lemma `fib-aux-fib-lemma` above.

*Hint*: You will probably want to use `+-step` from
[natural-numbers-functions](../natural-numbers-functions.lagda.md) at some
point.

### References

The exercises and solutions of Part 2 were based on [Neil Mitchell's
proof][mitchell] in the programming language [Idris][idris].

[mitchell]: http://neilmitchell.blogspot.com/2017/05/proving-fib-equivalence.html
[idris]: https://en.wikipedia.org/wiki/Idris_(programming_language)
