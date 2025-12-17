# Week 02 - Agda Exercises

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

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
exfalso : ∀{A : Set} → 𝟘 → A
exfalso ()

[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = inl a , inl b
[i] (inr c) = inr c , inr c

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] f = (λ a → f (inl a)) , λ b → f (inr b)

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] x = {!!} -- we don't know which of A or B might be empty

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f nb a = nb (f a)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] f b = {!!} -- We do get that a is not false, but dne does not hold here.

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = {!!} -- Pierce's law, implies LEM

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] = λ z a z₁ → z (a , z₁)

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] = {!!} -- Cannot construct a witness from a contradiction.

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] f = (λ a → f a .pr₁) , (λ a → f a .pr₂)
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne ta a = ta (λ da → da a)
-- λ z z₁ → z (λ z₂ → z₂ z₁)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f nna nb = nna (λ a → nb (f a))


¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f nna nb = nna (λ a → f a nb)
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true  = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ _ _ (refl true)  = (λ _ → ⋆) , (λ _ → ⋆)
bool-≡-char₁ _ _ (refl false) = ((λ ())   ,  λ ())
```


### Exercise 3 (★★)

Using ex. 2, conclude that
```agda
true≢false : ¬ (true ≡ false)
true≢false p = bool-≡-char₁ true false p .pr₁ ⋆
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true  true  _ = refl true
bool-≡-char₂ true  false (f , _) with f ⋆
... | ()
bool-≡-char₂ false true  (_ , g) with g ⋆
... | ()
bool-≡-char₂ false false _ = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that

```agda
data Singleton {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {A : Set} (x : A) → Singleton x
inspect x = x with≡ refl x

bothTrueAndFalse : (x : Bool) → x ≡ true → x ≡ false → 𝟘
bothTrueAndFalse _ (refl _) ()


decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A .pr₁ discA = f , f-decides
   where
     sumtoBool : ∀ {a b : A} → is-decidable (a ≡ b) → Bool
     sumtoBool (inl _) = true
     sumtoBool (inr _) = false

     sumtoBool-refl : ∀ {x : A} → (d : is-decidable (x ≡ x)) → sumtoBool d  ≡ true
     sumtoBool-refl (inl y) = refl (sumtoBool (inl y))
     sumtoBool-refl {x} (inr n) = 𝟘-nondep-elim (n (refl x))

     f : A → A → Bool
     f a b = sumtoBool (discA a b)

     f-decides : (x y : A) → x ≡ y ⇔ f x y ≡ true
     f-decides x .x .pr₁ (refl .x) = sumtoBool-refl (discA x x)
     f-decides x y .pr₂ with discA x y
     ... | inl a = λ _ → a
     ... | inr _ = λ f≡t → 𝟘-nondep-elim (bothTrueAndFalse false f≡t (refl false))

decidable-equality-char A .pr₂ (f , biimp) a b with biimp a b | inspect (f a b) 
... | ( _ , g ) | true with≡ f≡true = inl (g f≡true)
... | (g , _ ) | false with≡ f≡false = inr λ a≡b → bothTrueAndFalse (f a b) (g a≡b) f≡false
```
