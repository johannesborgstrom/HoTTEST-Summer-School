
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module snippets where

open import prelude
```
-->

## PathFroms and PathFrom equality, using Pauline Möhring's variant of J

```agda
PathFrom : {A : Set} -> A -> Set
PathFrom {A} M = Σ y ꞉ A , M ≡ y

J' : (A : Set) (M : A) (C : PathFrom M -> Set)
      -> C (M , refl M) 
      -> (P : PathFrom M) -> C P
J' A M C b (.M , refl M) = b


EPrefl : ∀ {A : Set} {M : A} → (P : PathFrom M) → P ≡ (M , refl M)
EPrefl {A} {M} = J' A M (λ P' → P' ≡ (M , refl M)) (refl (M , refl M))

EP : ∀ {A : Set} {M : A} → (P1 P2 : PathFrom M) → P1 ≡ P2
EP {A} {M} P1 P2 = P1 ≡⟨ EPrefl P1 ⟩ (M , refl M) ≡⟨ sym (EPrefl P2) ⟩ P2 ∎

```


## "inspect" function for augmenting pattern matching with paths


```agda
data Singleton {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {A : Set} (x : A) → Singleton x
inspect x = x with≡ refl x
```
