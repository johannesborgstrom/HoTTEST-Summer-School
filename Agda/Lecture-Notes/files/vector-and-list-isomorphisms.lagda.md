
[Martin Escardo](Https://www.Cs.Bham.Ac.Uk/~mhe/).
Notes originally written for the module *Advanced Functional Programming* of the [University of Birmingham](https://www.birmingham.ac.uk/index.aspx), UK.


<!--
```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module vector-and-list-isomorphisms where

open import prelude
open import natural-numbers-functions
```
-->
# Vector and list isomorphisms

There are deliberate gaps in this file for you to fill.

## The type of lists can be defined from that of vectors

```agda
open import isomorphisms

lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → Σ n ꞉ ℕ , Vector A n
  f [] = 0 , []
  f (x :: xs) with f xs 
  ... | (n , vec) = suc n , x :: vec

  g : (Σ n ꞉ ℕ , Vector A n) → List A
  g (_ , []) = []
  g (suc n , x :: vec) = x :: g (n , vec)

  gf : g ∘ f ∼ id
  gf [] = refl []
  gf (x :: xs) = ap (x ::_) (gf xs)

  fg : f ∘ g ∼ id
  fg (0 , []) = refl (zero , [])
  fg (suc n , x :: vec) = ap addx (fg (n , vec))
    where
      addx : (Σ m ꞉ ℕ , Vector A m) → (Σ m ꞉ ℕ , Vector A m)
      addx (n , xs) = suc n , x :: xs 

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

## The type of vectors can be defined from that of lists

```agda
open import List-functions

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

vectors-from-lists : {A : Type} (n : ℕ) → Vector A n ≅ (Σ xs ꞉ List A , (length xs ≡ n))
vectors-from-lists {A} n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : ∀ m → Vector A m → Σ xs ꞉ List A , (length xs ≡ m)
  f 0 [] = [] , refl 0
  f (suc m) (x :: vec) with f m vec
  ... | (xs , lxsn) = (x :: xs) , ap suc lxsn

  pred-suc-id : ∀ {m n : ℕ} → m ≡ n → pred (suc m) ≡ n
  pred-suc-id r = r

  lift-pred-suc-id : ∀ {m n : ℕ} → (m≡n : m ≡ n) → ap pred (ap suc m≡n) ≡ m≡n
  lift-pred-suc-id {m} {n} m≡n = ap {!!} ep 
    where
      ep : (n , ap pred (ap suc m≡n)) ≡ (n , m≡n)
      ep = EP {ℕ} {m} (n , ap pred (ap suc m≡n)) (n , m≡n) 
  -- ≡-elim (λ x y r → {!!}) (λ x → {!!}) m n {!!}

  lift-compose-refl : (f g : ℕ → ℕ) → ∀ n → ap f (ap g (refl n)) ≡ refl (f (g n))
  lift-compose-refl f g n = refl (ap f (ap g (refl n)))

  g : ∀ m → ( Σ xs ꞉ List A , (length xs ≡ m)) →  Vector A m
  g zero (_ , _) = [] 
  g (suc m) (x :: xs , lxsn) = x :: g m (xs , ap pred lxsn)

  gf : ∀ m → (g m) ∘ (f m) ∼ id
  gf zero [] = refl []
  gf (suc m) (x :: xs) with gf m xs
  ... | IH = ap (x ::_ ) ((g m (f m xs .pr₁ , ap pred (ap suc (f m xs .pr₂))))
                   ≡⟨ ap (λ z → g m (f m xs .pr₁ , z)) (lift-pred-suc-id (f m xs .pr₂)) ⟩
                       (g m (f m xs .pr₁ , f m xs .pr₂))
                   ≡⟨ IH ⟩
                       xs
                   ∎)


  fg : ∀ m → (f m) ∘ (g m) ∼ id
  fg zero ([] , refl zero) = refl ([] , refl zero)
  fg (suc m) (x :: xs , lxsn) with fg m (xs , ap pred lxsn)
  ... | IH = ap {! addx !}  IH
    where
      addx : (Σ ys ꞉ List A , (length ys ≡ m)) → (Σ ys ꞉ List A , (length ys ≡ suc m))
      addx (ys , p) with inspect (length ys)
      ... | _ with≡ _ = x :: ys , ap suc p

  f-is-bijection : ∀ n → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n }
```

## The types of lists and vectors can be defined in basic MLTT

```agda
Vector' : (A : Type) → ℕ → Type
Vector' A 0       = 𝟙
Vector' A (suc n) = A × Vector' A n

[]' : {A : Type} → Vector' A 0
[]' = ⋆

_::'_ : {A : Type} {n : ℕ} → A → Vector' A n → Vector' A (suc n)
x ::' xs = x , xs

List' : Type → Type
List' X = Σ n ꞉ ℕ , Vector' X n

```

```agda
vectors-in-basic-MLTT : {A : Type} (n : ℕ) → Vector A n ≅ Vector' A n
vectors-in-basic-MLTT {A} n = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : {n : ℕ} → Vector A n → Vector' A n
  f [] = ⋆
  f (x :: xs) = x , f xs

  g : ∀ n → Vector' A n → Vector A n
  g zero ⋆ = []
  g (suc n) (x , xs) = x :: g n xs

  gf : ∀ n → (g n) ∘ f ∼ id
  gf 0 [] = refl []
  gf (suc n) (x :: xs) = ap (x ::_) (gf n xs)

  fg : ∀ n → f ∘ (g n) ∼ id
  fg zero ⋆ = refl _
  fg (suc n) (x , xs) = ap (x ,_) (fg n xs)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g n ; η = gf n ; ε = fg n }
```

```
lists-in-basic-MLTT : {A : Type} → List A ≅ List' A
lists-in-basic-MLTT {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → List' A
  f [] = zero , ⋆
  f (x :: xs) with f xs
  ... | (n , vec) = suc n , x , vec

  g : List' A → List A
  g (zero , ⋆) = []
  g (suc n , x , xs) = x :: g (n , xs)

  gf : g ∘ f ∼ id
  gf [] = refl _
  gf (x :: xs) = ap (x ::_) (gf xs)

  fg : f ∘ g ∼ id
  fg (zero , ⋆) = refl _
  fg (suc n , x , xsv) = ap addx (fg (n , xsv))
    where
      addx : List' A → List' A
      addx (m , xs) = (suc m) , x , xs

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

[Go back to the table of contents](https://martinescardo.github.io/HoTTEST-Summer-School/)
