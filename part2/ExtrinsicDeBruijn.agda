module plfa.part2.ExtrinsicDeBruijn where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import plfa.part2.DeBruijn using (Context; ∅; _,_; Type; `ℕ; _⇒_; length; lookup) -- hiding (plus; count; #_; _∋_; Z; S_)
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
  Z : ∀ {Γ A}
    -- → {x∈Γ : True (suc x ≤? length Γ)}
      ------------------
    → Γ , A ∋ zero ⦂ A

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

free : Term
free = `suc (` 0)

⊢free : ∀ {Γ} → Γ ⊢ free ⦂ `ℕ
⊢free = ⊢suc (⊢` {!   !})

ext : ∀ {Γ Δ}
  → (∀ {A n} →       Γ ∋ n ⦂ A →     Δ ∋ n ⦂ A)
    ---------------------------------
  → (∀ {A B n} → Γ , B ∋  n ⦂ A → Δ , B ∋  n ⦂ A)
ext ρ Z = Z
ext ρ (S `n) = S (ρ `n)

ext′ : (Var → Var) → Var → Var
ext′ ρ zero = zero
ext′ ρ (suc n) = suc (ρ n)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A) -- ? 这个 rename 不太对吧 （）
rename ρ (⊢` x) = ⊢` (ρ x)
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  = ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)

rename′ : (Var → Var) → ℕ → Term → Term -- renaming the free variables
rename′ ρ depth (` x) with x ≤? depth -- if something goes wrong, change to < instead of <=
... | yes _ = ` x
... | no  _ = ` (ρ x)
rename′ ρ depth (ƛ term) = ƛ (rename′ ρ (suc depth) term)
rename′ ρ depth (term · term₁) = (rename′ ρ depth term) · (rename′ ρ depth term₁)
rename′ ρ depth `zero = `zero
rename′ ρ depth (`suc term) = `suc (rename′ ρ depth term)
rename′ ρ depth case term [zero⇒ term₁ |suc⇒ term₂ ] = case (rename′ ρ depth term) [zero⇒ (rename′ ρ depth term₁) |suc⇒ (rename′ ρ (suc depth) term₂) ]
rename′ ρ depth (μ term) = μ (rename′ ρ depth term)

exts′ : ∀ {Γ Δ}
  → (∀ {A x} →       Γ ∋ x ⦂ A →     Δ ⊢ ` x ⦂ A)
    ---------------------------------
  → (∀ {A B x} → Γ , B ∋ x ⦂ A → Δ , B ⊢ ` x ⦂ A)
exts′ σ Z = ⊢` Z
exts′ σ (S ∋x) = {!   !} where
  aaa = σ ∋x -- `x : A

exts : (Var → Term) → Var → Term
exts σ zero = ` zero
exts σ (suc n) = rename′ suc zero (σ n)


exts-pres : ∀ {Γ Δ σ}
  → (∀ {A x}  →      Γ ∋ x ⦂ A →            Δ ⊢ σ x ⦂ A)
    ----------------------------------------------------
  → (∀ {A B x} → Γ , B ∋ x ⦂ A → Δ , B ⊢ (exts σ) x ⦂ A)
exts-pres ρ Z = ⊢` Z
exts-pres ρ (S ∋x) = {!  !} where
  aab = ρ ∋x