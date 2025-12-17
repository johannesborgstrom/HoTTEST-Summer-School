# Week 03 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 03-Exercises where

open import prelude hiding (_∼_)
```

## Part I -- Homotopies

It is often convenient to work with *pointwise equality* of functions, defined as follows.
```agda
module _ {A : Type} {B : A → Type} where
  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Type
  f ∼ g = ∀ x → f x ≡ g x
```
An element of `f ∼ g` is usually called a homotopy.

### Exercise 1 (⋆⋆)

Unsurprisingly, many properties of this type of pointwise equalities
can be inferred directly from the same operations on paths.

Try to prove reflexivity, symmetry and transitivity of `_∼_` by filling these holes.
```agda
  ∼-refl : (f : (x : A) → B x) → f ∼ f
  ∼-refl f x = refl (f x)

  ∼-inv : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  ∼-inv f g H x = sym (H x)

  ∼-concat : (f g h : (x : A) → B x) → f ∼ g → g ∼ h → f ∼ h
  ∼-concat f g h H K x = trans (H x) (K x)

  infix 0 _∼_
```

## Part II -- Isomorphisms

A function `f : A → B` is called a *bijection* if there is a function `g : B → A` in the opposite direction such that `g ∘ f ∼ id` and `f ∘ g ∼ id`. Recall that `_∼_` is [pointwise equality](../Lecture-Notes/files/identity-type.lagda.md) and that `id` is the [identity function](../Lecture-Notes/files/products.lagda.md). This means that we can convert back and forth between the types `A` and `B` landing at the same element we started with, either from `A` or from `B`. In this case, we say that the types `A` and `B` are *isomorphic*, and we write `A ≅ B`. Bijections are also called type *isomorphisms*. We can define these concepts in Agda using [sum types](../Lecture-Notes/files/sums.lagda.md) or [records](https://agda.readthedocs.io/en/latest/language/record-types.html). We will adopt the latter, but we include both definitions for the sake of illustration.
Recall that we [defined](../Lecture-Notes/files/general-notation.lagda.md) the domain of a function `f : A → B` to be `A` and its codomain to be `B`.

We adopt this definition of isomorphisms using records.
```agda
record is-bijection {A B : Type} (f : A → B) : Type where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_
```

### Exercise 2 (⋆)

Reformulate the same definition using Sigma-types.
```agda
is-bijection' : {A B : Type} → (A → B) → Type
is-bijection' {A} {B} f = Σ g ꞉ (B → A) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

_≅'_ : Type → Type → Type
A ≅' B = Σ f ꞉ (A → B) , is-bijection' f  
```
The definition with `Σ` is probably more intuitive, but, as discussed above,
the definition with a record is often easier to work with,
because we can easily extract the components of the definitions using the names of the fields.
  It also often allows Agda to infer more types, and to give us more sensible goals in the
interactive development of Agda programs and proofs.

Notice that `inverse` plays the role of `g`.
The reason we use `inverse` is that then we can use the word
`inverse` to extract the inverse of a bijection.
Similarly we use `bijection` for `f`, as we can use the word
`bijection` to extract the bijection from a record.

This type can be defined to be `𝟙 ∔ 𝟙` using the coproduct,
but we give a direct definition which will allow us to discuss some relationships between the various type formers of Basic MLTT.

```agda
data 𝟚 : Type where
 𝟎 𝟏 : 𝟚
```

### Exercise 3 (⋆⋆)

Prove that 𝟚 and Bool are isomorphic

```agda
Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f false = 𝟎 
  f true  = 𝟏 

  g : 𝟚 → Bool
  g 𝟎 = false
  g 𝟏 = true

  gf : g ∘ f ∼ id
  gf true  = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```


## Part III - Finite Types

In the last HoTT Exercises we encountered two definitions of the finite types.
Here we prove that they are isomorphic.
Note that `zero` was called `pt` and suc `i` on the HoTT exercise sheet.

```agda
data Fin : ℕ → Type where
 zero : {n : ℕ} → Fin (suc n)
 suc  : {n : ℕ} → Fin n → Fin (suc n)
```

### Exercise 4 (⋆)

Prove the elimination principle of `Fin`.
```agda
Fin-elim : (A : {n : ℕ} → Fin n → Type)
         → ({n : ℕ} → A {suc n} zero)
         → ({n : ℕ} (k : Fin n) → A k → A (suc k))
         → {n : ℕ} (k : Fin n) → A k
Fin-elim A a f = h
 where
  h : {n : ℕ} (k : Fin n) → A k
  h zero    = a
  h (suc k) = f k (h k)
```

We give the other definition of the finite types and introduce some notation.

```agda
Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr
```

### Exercise 5 (⋆⋆⋆)

Prove that `Fin n` and `Fin' n` are isomorphic for every `n`.

```agda
Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero    = inl ⋆
  f (suc n) (suc k) = inr (f n k)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr k) = suc (g n k)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero    = refl zero
  gf (suc n) (suc k) = γ
   where
    IH : g n (f n k) ≡ k
    IH = gf n k

    γ = g (suc n) (f (suc n) (suc k)) ≡⟨ refl _ ⟩
        g (suc n) (suc' (f n k))      ≡⟨ refl _ ⟩
        suc (g n (f n k))             ≡⟨ ap suc IH ⟩
        suc k                         ∎

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (inl ⋆) = refl (inl ⋆)
  fg (suc n) (inr k) = γ
   where
    IH : f n (g n k) ≡ k
    IH = fg n k

    γ = f (suc n) (g (suc n) (suc' k)) ≡⟨ refl _ ⟩
        f (suc n) (suc (g n k))        ≡⟨ refl _ ⟩
        suc' (f n (g n k))             ≡⟨ ap suc' IH ⟩
        suc' k                         ∎

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}
```

## Part IV -- minimal elements in the natural numbers

In this section we establish some definitions which are needed to state and prove the well-ordering
principle of the natural numbers.

### Exercise 6 (⋆)

Give the recursive definition of the less than or equals relation on the natural numbers.

```agda
_≤₁_ : ℕ → ℕ → Type
0     ≤₁ y     = 𝟙
suc x ≤₁ 0     = 𝟘
suc x ≤₁ suc y = x ≤₁ y
```

### Exercise 7 (⋆)

Given a type family `P` over the naturals, a lower bound `n` is a natural number such that
for all other naturals `m`, we have that if `P(m)` holds, then`n ≤₁ m`.
Translate this definition into HoTT.

```agda
is-lower-bound : (P : ℕ → Type) (n : ℕ) → Type
is-lower-bound P n = (m : ℕ) → (A : P m) → n ≤₁ m 
```

We define the type of minimal elements of a type family over the naturals.
```agda
minimal-element : (P : ℕ → Type) → Type
minimal-element P = Σ n ꞉ ℕ , (P n) × (is-lower-bound P n)
```

### Exercise 8 (⋆)

Prove that all numbers are at least as large as zero.
```agda
leq-zero : (n : ℕ) → 0 ≤₁ n
leq-zero zero    = ⋆
leq-zero (suc n) = leq-zero n
```


## Part V -- The well-ordering principle of ℕ

Classically, the well-ordering principle states that every non-empty set
of natural numbers has a least element.

In HoTT, such subsets can be translated as decidable type family.
Recall the definition of decidability:
```agda
open import decidability
  using (is-decidable; is-decidable-predicate)
```

The well-ordering principle reads
```agda
Well-ordering-principle = (P : ℕ → Type) → (d : is-decidable-predicate P) → (n : ℕ) → P n → minimal-element P
```

We shall prove this statement via induction on `n`.
In order to make the proof more readable, we first prove two lemmas.

### Exercise 9 (🌶)

What is the statement of `is-minimal-element-suc`
under the Curry-Howard interpretation?
Prove this lemma.

```agda
is-minimal-element-suc :
  {P : ℕ → Type}  {m : ℕ}  →
  (is-lower-bound (λ x → P (suc x)) m) →
  ¬ (P 0) →
  is-lower-bound P (suc m)
is-minimal-element-suc _ neg-p0 zero A = 𝟘-nondep-elim (neg-p0 A)
is-minimal-element-suc is-lower-bound _ (suc n) A = is-lower-bound n A
``` 

### Exercise 10 (🌶)

What is the statement of `well-ordering-principle-suc`
under the Curry-Howard interpretation?
Prove this lemma.

```agda
well-ordering-principle-suc :
  (P : ℕ → Type) → is-decidable (P 0) →
  minimal-element (λ m → P (suc m)) → minimal-element P
well-ordering-principle-suc P (inl p0) _  = zero , p0 , (λ m A → ⋆)
well-ordering-principle-suc P (inr neg-p0) (m , (pm , is-min-m)) =
  suc m , (pm , is-minimal-element-suc is-min-m neg-p0)
```

### Exercise 11 (🌶)

Use the previous two lemmas to prove the well-ordering principle
```agda
well-ordering-principle : (P : ℕ → Type) → (d : is-decidable-predicate P) → (n : ℕ) → P n → minimal-element P
well-ordering-principle P d zero    p = zero , p , (λ m A → ⋆)
well-ordering-principle P d (suc n) p = well-ordering-principle-suc P (d 0)
    (well-ordering-principle (λ z → P (suc z)) (λ x → d (suc x)) n p)
```

### Exercise 12 (🌶)

Prove that the well-ordering principle returns 0 if `P 0` holds.

```agda
minimal-is-zero-if-P-zero : {P : ℕ → Type} (p0 : P 0) → (m : minimal-element P) → pr₁ m ≡ 0
minimal-is-zero-if-P-zero p0 (min , _ , min-is-minimal) with min-is-minimal zero p0
minimal-is-zero-if-P-zero _ (zero , _ , _) | _ = refl zero

is-zero-well-ordering-principle : (P : ℕ → Type) (d : is-decidable-predicate P) → (n : ℕ) → (pn : P n) →
  P 0 →  pr₁ (well-ordering-principle P d n pn) ≡ 0
is-zero-well-ordering-principle P d n pn p0 = minimal-is-zero-if-P-zero p0 (well-ordering-principle P d n pn)
```
