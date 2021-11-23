module plfa.part2.ExtrinsicDeBruijn where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import plfa.part2.DeBruijn hiding (plus; count; #_; _∋_; Z; S_)
-- let's do some exercise!

{-
Formalize the STLC using the extrinsic style,
as in Lambda, but using de Bruijn indices to represent variables,
as in DeBruijn. You should use the ext, rename, exts, and subst functions
from the DeBruijn chapter, simplifying the type declarations of those functions.
-}
Var : Set
Var = ℕ

infix  4  _⊢_⦂_
infix  4  _∋_⦂_
-- infixl 5 _,_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
-- infix  9 S_
-- infix  9 #_

data Term : Set where
  `_                      :  Var → Term
  ƛ_                    :  Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc⇒_]       :  Term → Term → Term → Term
  μ_                    :  Term → Term

-- 0 + n = n
-- s(m) + n = s(m + n)
plus : Term -- change back to lambda-style (i mean in lambda.agda)
plus = μ ƛ (ƛ case (` 1)
  [zero⇒ (` 0)
  |suc⇒ (`suc ((` 3) · (` 0) · (` 1))) ])

_ : Type
_ = `ℕ ⇒ `ℕ

data _∋_⦂_ : Context → Var → Type → Set where
  Z : ∀ {Γ A} {x : ℕ}
    → {x∈Γ : True (suc x ≤? length Γ)}
      ------------------
    → Γ ∋ x ⦂ A

  S_ : ∀ {Γ A B} {x : ℕ}
    -- → {x∈Γ : True (suc x ≤? length Γ)}
    → Γ ∋ x ⦂ A
    → Γ , B ∋ suc x ⦂ A
      ------------------


data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ⦂ A
  ⊢ƛ  : ∀ {Γ A B x}
    → Γ , A ⊢ x ⦂ B
      ---------
    → Γ ⊢ ƛ x ⦂ A ⇒ B
  _·_ : ∀ {Γ A B x y}
    → Γ ⊢ x ⦂ A ⇒ B
    → Γ ⊢ y ⦂ A
      ---------
    → Γ ⊢ x · y ⦂ B
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ
  ⊢case : ∀ {Γ M N L A}
    → Γ ⊢ M ⦂ `ℕ
    → Γ ⊢ N ⦂ A
    → Γ , `ℕ ⊢ L ⦂ A
    → Γ ⊢ case M [zero⇒ N |suc⇒ L ] ⦂ A
  ⊢μ : ∀ {Γ M A}
    → Γ , A ⊢ M ⦂ A
    → Γ ⊢ μ M ⦂ A

count : ∀ {Γ} → {n : Var} → (p : n < length Γ) → Γ ∋ n ⦂ lookup p
count {_ , _} {zero}    (s≤s z≤n)  =  Z
count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ ` n ⦂ lookup (toWitness n∈Γ)
#_ n {n∈Γ} = ⊢` (count (toWitness n∈Γ))

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (# 1) (# 0) (⊢suc (((# 3) · (# 0)) · (# 1))))))
