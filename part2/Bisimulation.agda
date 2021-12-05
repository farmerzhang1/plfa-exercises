module plfa.part2.Bisimulation where

open import plfa.part2.More
import Relation.Binary.PropositionalEquality as Eq
open import Data.Bool
open Eq using (_≡_; refl; cong; cong₂)

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_
infix  8 _†

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†

well : ∀ {Γ A} → Γ ⊢ A → Bool
well (` x) = true
well (ƛ x) = well x
well (x · x₁) = well x ∧ well x₁
well (`let x x₁) = well x ∧ well x₁
well _ = false

-- one : {a b : Bool} → T (a ∧ b) → T a
-- one aa = {!  !}

postulate
  one : {a b : Bool} → T (a ∧ b) → T a
  two : {a b : Bool} → T (a ∧ b) → T b

_† : ∀ {Γ A} → (m : Γ ⊢ A) → {T (well m)} → Γ ⊢ A
_† (` x₁) {x} = ` x₁
_† (ƛ m) {x} = ƛ (_† m {x})
_† (m · m₁) {x} = _† m {one x} · _† m₁ {two x}
_† (`let m m₁) {x} = (ƛ (_† m₁ {two x})) · (_† m {one x})

≡→~ : ∀ {Γ A} → {M N : Γ ⊢ A} → {jjj : T (well M)}
  → (_† M {jjj}) ≡ N
  → M ~ N
≡→~ {M = ` x} {N = .(` x †)} refl = ~`
≡→~ {M = ƛ M} {N = .((ƛ M) †)} refl = ~ƛ (≡→~ refl)
≡→~ {M = M · M₁} {N = .((M · M₁) †)} refl = (≡→~ refl) ~· (≡→~ refl)
≡→~ {M = `let M M₁} {N = .(`let M M₁ †)} refl = ~let (≡→~ refl) (≡→~ refl)

-- ≡→~
-- ~→≡

~→≡ : ∀ {Γ A} → {M N : Γ ⊢ A} → {jjj : T (well M)}
  → M ~ N
  → (_† M {jjj}) ≡ N
~→≡ {M = .(` _)} {N = .(` _)} ~` = refl
~→≡ {M = (ƛ x)} {N = (ƛ y)} (~ƛ ~~~) = cong ƛ_ (~→≡ ~~~)
~→≡ {M = (w · x)} {N = (y · z)} (L~L ~· M~M) = cong₂ _·_ (~→≡ L~L) (~→≡ M~M)
~→≡ {M = (`let w x)} {N = ((ƛ y) · z)} (~let M~M N~N) = cong₂ _·_ (~→≡ (~ƛ N~N)) (~→≡ M~M)
