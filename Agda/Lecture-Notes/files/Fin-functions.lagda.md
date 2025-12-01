
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Fin-functions where

open import prelude
open import natural-numbers-type
open import natural-numbers-functions
```
-->

# Isomorphism of Fin n with a Basic MLTT type

```agda
Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n

zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆

suc'  : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr

open import Fin
open import isomorphisms

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc n) zero    = zero'
  f (suc n) (suc k) = suc' (f n k)

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



data _<_ : ℕ → ℕ → Type where
 0-smallest      : {y : ℕ} → 0 < suc y
 suc-preserves-< : {x y : ℕ} → x < y → suc x < suc y

_>_ : ℕ → ℕ → Type
x > y = y < x

infix 0 _<_
infix 0 _>_



Fin-isomorphism-Σ< : (n : ℕ) → Fin n ≅ (Σ k ꞉ ℕ , k < n)
Fin-isomorphism-Σ< n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → (Σ k ꞉ ℕ , k < n)
  f (suc n) zero = 0 , 0-smallest
  f (suc n) (suc x) with f n x 
  ... | m , m<n = suc m , suc-preserves-< m<n

  g : (n : ℕ) → (Σ k ꞉ ℕ , k < n) → Fin n
  g (suc n) (zero , k<n) = zero
  g (suc n) (suc k , suc-preserves-< k<n) = suc (g n (k , k<n))

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero = refl ((g (suc n) ∘ f (suc n)) zero)
  gf (suc n) (suc x) = ap suc (gf n x)

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (zero , 0-smallest) = refl (zero , 0-smallest)
  fg (suc n) (suc m , suc-preserves-< m<n) = ap (sucSigma n) (fg n (m , m<n))
    where
        sucSigma : ∀ n → (Σ k ꞉ ℕ , k < n) → (Σ k ꞉ ℕ , k < suc(n))
        sucSigma _ (k , k<n) = suc k , suc-preserves-< k<n

 
  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}
```

**Exercise.** Show that the type `Fin n` is isomorphic to the type `Σ k : ℕ , k < n`.

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
