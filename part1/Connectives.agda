module agda.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import agda.part1.Isomorphism using (_≃_; _≲_; extensionality)
open agda.part1.Isomorphism.≃-Reasoning

infixr 2 _×_
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl } -- Replacing the definition of from∘to by λ w → refl will not work
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C) -- god damn it !!! 是×不是x
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

data ⊤ : Set where

  tt :
    --
    ⊤
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

data _⊎_ (A B : Set) : Set where -- so pretty!

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y
                                  -- 注意优先级！！！
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → (case-⊎ inj₁ inj₂ w) ≡ w -- 这个也好难啊!(懂了)
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

-- case-⊎
⊎-comm : ∀ {A B : Set}
  → A ⊎ B
  → B ⊎ A
⊎-comm (inj₁ x) = inj₂ x
⊎-comm (inj₂ y) = inj₁ y

⊎-assoc : ∀ {A B C : Set}
  → A ⊎ (B ⊎ C)
  → (A ⊎ B) ⊎ C
⊎-assoc (inj₁ x) = inj₁ (inj₁ x)
⊎-assoc (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
⊎-assoc (inj₂ (inj₂ z)) = inj₂ z

data ⊥ : Set where
  -- no clauses!

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

⊥-identityˡ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityˡ =
  record {
    to = λ { (inj₁ x) → x };
    from = λ { x → (inj₁ x) };
    from∘to = λ { (inj₁ x) → refl };
    to∘from = λ { x → refl }
  }

⊥-identityʳ : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊥-identityʳ {A} =
  record {
    to = λ { (inj₂ x) → x };
    from = λ { x → (inj₂ x) };
    from∘to = λ { (inj₂ x) → refl };
    to∘from = λ { x → refl }
  }
  -- ≃-begin
  --   (⊥ ⊎ A)
  -- ≃⟨ ⊎-comm ⟩ -- it isn't isomorphism!
  --   (A ⊎ ⊥)
  -- ≃⟨ ⊥-identityˡ ⟩
  --   A
  -- ≃-∎

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }