# Week 7 - Cubical Agda Exercises

## Standard disclaimer:

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

In case you haven't done the other Agda exercises:
This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**When solving the problems,
please make a copy of this file to work in, so that it doesn't get overwritten
(in case we update the exercises through `git`)!**


```agda
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Exercises7 where

open import cubical-prelude
open import Lecture7-notes
```

```agda
private
  variable
    A : Type ℓ
    B : A → Type ℓ
```

## Part I: Generalizing to dependent functions

### Exercise 1 (★)

State and prove funExt for dependent functions `f g : (x : A) → B x`
```agda
depFunExt : {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g
depFunExt f∼g i x = f∼g x i
```
### Exercise 2 (★)

Generalize the type of ap to dependent function `f : (x : A) → B x`
(hint: the result should be a `PathP`)
```agda
depAp : (f : (x : A) → B x) {x y : A} → (p : x ≡ y)
      → PathP (λ j → B (p j)) (f x) (f y)
depAp f p i = f (p i)
```


## Part II: Some facts about (homotopy) propositions and sets

The first three homotopy levels `isContr`, `isProp` and `isSet`
are defined in `cubical-prelude` in the usual way
(only using path types of course).

### Exercise 3 (★)

State and prove that inhabited propositions are contractible
```agda
isContrProp : isProp A → A → isContr A
isContrProp isp a = a , isp a
```


### Exercise 4 (★)

Prove

```agda
isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h f g = depFunExt (λ x → h x (f x) (g x))
```

### Exercise 5 (★)

Prove the inverse of `funExt` (sometimes called `happly`):

```agda
funExt⁻ : {f g : (x : A) → B x} → f ≡ g → ((x : A) → f x ≡ g x)
funExt⁻ p x i = p i x
```

### Exercise 6 (★★)

Use funExt⁻ to prove isSetΠ:

```agda
isSetΠ : (h : (x : A) → isSet (B x)) → isSet ((x : A) → B x)
isSetΠ h f g p q = {!!} 
```

### Exercise 7 (★★★): alternative contractibility of singletons

We could have defined the type of singletons as follows

```agda
singl' : {A : Type ℓ} (a : A) → Type ℓ
singl' {A = A} a = Σ x ꞉ A , x ≡ a
```

Prove the corresponding version of contractibility of singetons for
`singl'` (hint: use a suitable combinations of connections and `~_`)

```agda
isContrSingl' : (x : A) → isContr (singl' x)
isContrSingl' x = (x , refl) , (λ (y , p) i → p (~ i) , λ j → p (j ∨ (~ i)))
```

## Part III: Equality in Σ-types
### Exercise 8 (★★)

Having the primitive notion of equality be heterogeneous is an
easily overlooked, but very important, strength of cubical type
theory. This allows us to work directly with equality in Σ-types
without using transport.

Fill the following holes (some of them are easier than you might think):

```agda
module _ {A : Type ℓ} {B : A → Type ℓ'} {x y : Σ A B} where

  ΣPathP : Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
         → x ≡ y
  ΣPathP (fst , snd) i = fst i , snd i

  PathPΣ : x ≡ y
         → Σ p ꞉ pr₁ x ≡ pr₁ y , PathP (λ i → B (p i)) (pr₂ x) (pr₂ y)
  PathPΣ q = (λ i → q i .pr₁) , (λ i → q i .pr₂)

  ΣPathP-PathPΣ : ∀ p → PathPΣ (ΣPathP p) ≡ p
  ΣPathP-PathPΣ p _ = (p .pr₁) , (p .pr₂)

  PathPΣ-ΣPathP : ∀ p → ΣPathP (PathPΣ p) ≡ p
  PathPΣ-ΣPathP p _ j = (p j .pr₁) , (p j .pr₂)
```

If one looks carefully the proof of prf in Lecture 7 uses ΣPathP
inlined, in fact this is used all over the place when working
cubically and simplifies many proofs which in Book HoTT requires long
complicated reasoning about transport.


## Part IV: Some HITs

Now we want prove some identities of HITs analogous to `Torus ≡ S¹ × S¹`
Hint: you can just use `isoToPath` in all of them.


### Exercise 9 (★★)

We saw two definitions of the torus:
`Torus` having a dependent path constructor `square`
and `Torus'` with a path constructor `square` that involves composition.

Using these two ideas, define the *Klein bottle* in two different ways.

```agda
data Klein : Type₀ where
  point : Klein
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 (~ i) ≡ line1 i) line2 line2
```


### Exercise 10 (★★)

Prove

```agda
suspUnitChar : Susp Unit ≡ Interval
suspUnitChar = isoToPath (iso f g fg gf)
  where
    f : Susp Unit → Interval
    f north       = zero
    f south       = one
    f (merid _ i) = seg i

    g : Interval → Susp Unit
    g zero    = north
    g one     = south
    g (seg i) = merid ⋆ i

    fg : section f g
    fg zero    = refl
    fg one     = refl
    fg (seg i) = refl

    gf : retract f g
    gf north       = refl
    gf south       = refl
    gf (merid _ i) = refl
```


### Exercise 11 (★★★)

Define suspension using the Pushout HIT and prove that it's equal to Susp.


### Exercise 12 (🌶)

The goal of this exercise is to prove

```agda
suspBoolChar : Susp Bool ≡ S¹
suspBoolChar = isoToPath (iso f g fg gf)
  where
  f : Susp Bool → S¹
  f north = base
  f south = base
  f (merid true i) = loop i
  f (merid false i) = refl {_} {_} {base} i

  g : S¹ → Susp Bool
  g base = north
  g (loop i) = (merid true ∙ sym (merid false)) i

  fg : section f g
  fg base = refl
  fg (loop i) j = {!!}

  gf : retract f g
  gf north = refl
  gf south = {!!}
  gf (merid true i) j = {!(merid true ∙ sym (merid false)) (i ∧ ~ j)!}
  gf (merid false i) j = {!!}
```

For the map `Susp Bool → S¹`, we have to specify the behavior of two
path constructors. The idea is to map one to `loop` and one to `refl`.

For the other direction, we have to fix one base point in `Susp Bool`
and give a non-trivial loop on it, i.e. one that shouldn't cancel out
to `refl`.

Proving that the two maps cancel each other requires some primitives
of `Cubical Agda` that we won't really discuss in the lectures,
namely `hcomp` and `hfill`. These are used (among other things)
to define path composition and ensure that it behaves correctly.

Path composition corresponds to the top of the following square:

```text
            p∙q
       x --------> z
       ^           ^
       ¦           ¦
  refl ¦     sq    ¦ q
       ¦           ¦
       ¦           ¦
       x --------> y
             p
```

The type of `sq` is a `PathP` sending `p` to `p ∙ q`
over `q` and the following lemma lets us construct such a *square*:

```agda
comp-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
            → PathP (λ j → refl {x = x} j ≡ q j) p (p ∙ q)
comp-filler {x = x} p q j i = hfill (λ k → λ { (i = i0) → x
                                              ; (i = i1) → q k })
                                    (inS (p i)) j
```

You can use this `comp-filler` as a black-box for proving the round-trips
in this exercise.

**Hint:** For one of the round-trips you only need the following familiar
result, that is a direct consequence of `comp-filler` in `Cubical Agda`

```agda
rUnit : {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
rUnit p = sym (comp-filler p refl)
```
