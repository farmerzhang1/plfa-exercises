module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import plfa.part1.Isomorphism renaming (_∘_ to _hahaha_)
open import plfa.part2.Lambda

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

infix  4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where

  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    -----------
  → Canonical V ⦂ A
canonical (⊢` t) ()
canonical (⊢ƛ t) v = C-ƛ t
canonical (⊢zero) v = C-zero
canonical (a · b) ()
canonical (⊢suc j) (V-suc v) = C-suc (canonical j v)
canonical (⊢case n z s) ()
canonical (⊢μ j) ()

value : ∀ {M A}
  → Canonical M ⦂ A
    ----------------
  → Value M
value (C-ƛ ⊢N)    =  V-ƛ
value C-zero      =  V-zero
value (C-suc CM)  =  V-suc (value CM)

typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N)    =  ⊢ƛ ⊢N
typed C-zero      =  ⊢zero
typed (C-suc CM)  =  ⊢suc (typed CM)

data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done VL with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ VL M—→M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...   | C-zero                              =  step β-zero
...   | C-suc CL                            =  step (β-suc (value CL))
progress (⊢μ ⊢M)                            =  step β-μ

Progress-≃ : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ {M} = record {
  to = to
  ; from = from
  ; to∘from = to∘from
  ; from∘to = from∘to
  } where
  to : Progress M → Value M ⊎ ∃[ N ](M —→ N)
  to (done VM) = inj₁ VM
  to (step {N} m2n) = inj₂ ⟨ N , m2n ⟩
  from : Value M ⊎ ∃[ N ](M —→ N) → Progress M
  from (inj₁ x) = done x
  from (inj₂ ⟨ fst , snd ⟩) = step snd
  from∘to : ∀ (x : Progress M) → (from ∘ to) x ≡ x
  from∘to (step x) = refl
  from∘to (done x) = refl
  to∘from : ∀ (x : Value M ⊎ ∃[ N ](M —→ N)) → (to ∘ from) x ≡ x
  to∘from (inj₁ x) = refl
  to∘from (inj₂ y) = refl

progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ .(ƛ _ ⇒ _) {.(_ ⇒ _)} (⊢ƛ x) = inj₁ V-ƛ
progress′ (m1 · m2) {A} (x1 · x2) with progress′ _ x1 -- don't why agda's auto case split yields a . (delete it)
... | inj₂ ⟨ fst , snd ⟩ = inj₂ ⟨ (fst · m2) , ξ-·₁ snd ⟩
... | inj₁ vm1 with progress′ _ x2
...   | inj₂ ⟨ fst , snd ⟩ = inj₂ ⟨ (m1 · fst) , (ξ-·₂ vm1 snd) ⟩
...   | inj₁ vm2 with canonical x1 vm1
...     | C-ƛ {x} {A} {N} _ = inj₂ ⟨ N [ x := m2 ] , β-ƛ vm2 ⟩ -- 这也太难了()
progress′ .`zero {.`ℕ} ⊢zero = inj₁ V-zero
progress′ (`suc m) {.`ℕ} (⊢suc x) with progress′ m x
... | inj₁ x₁ = inj₁ (V-suc x₁)
... | inj₂ ⟨ fst , snd ⟩ = inj₂ ⟨ `suc fst , ξ-suc snd ⟩
progress′ (case m [zero⇒ z |suc m′ ⇒ n ]) {A} (⊢case x x₁ x₂) with progress′ m x
... | inj₂ ⟨ fst , snd ⟩ = inj₂ ⟨ case fst [zero⇒ z |suc m′ ⇒ n ] , ξ-case snd ⟩
... | inj₁ vm with canonical x vm
... | C-zero = inj₂ ⟨ z , β-zero ⟩
... | C-suc {V} z₁ = inj₂ ⟨ n [ m′ := V ] , (β-suc (value z₁)) ⟩
progress′ (μ x ⇒ m) {A} (⊢μ y) = inj₂ ⟨ m [ x := μ x ⇒ m ] , β-μ ⟩

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | done VM   = yes VM
... | step M—→M′ = no (—→¬V M—→M′)

