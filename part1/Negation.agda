module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,′_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

infix 3 ¬_

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A -- aka. (A → ⊥) → ⊥
¬¬-intro x  =  λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢  y  =  ¬ (x ≡ y)

_ : 1 ≢  2
_ = λ()

-- Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n.

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

irreflexive : {n : ℕ} → ¬ (n < n)
irreflexive (s<s n<n) = irreflexive n<n

-- demorgan : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
-- demorgan = record
--   {
--     to = λ{ f →  (λ{ a → f (inj₁ a) }) ,′ λ{ b → f (inj₂ b) } } ;
--     from = λ{ fa ,′ fb → ? };
--     from∘to = {!   !} ;
--     to∘from = {!   !}
--   }

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ {a → k (inj₁ a)})
