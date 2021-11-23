module plfa.part2.ExtrinsicDeBruijn where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import plfa.part2.DeBruijn
-- let's do some exercise!

{-
Formalize the STLC using the extrinsic style,
as in Lambda, but using de Bruijn indices to represent variables,
as in DeBruijn. You should use the ext, rename, exts, and subst functions
from the DeBruijn chapter, simplifying the type declarations of those functions.
-}
Var : Set
Var = ℕ

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
  case       :  Term → Term → Term → Term
  μ_                    :  Term → Term

-- 0 + n = n
-- s(m) + n = s(m + n)
_ : Term
_ = μ ƛ (ƛ case (` 1)  (` 0) ((` 3) · ((` 0) · (` 1))))

_ : Type
_ = `ℕ ⇒ `ℕ

_ : Context
_ = ∅ , (`ℕ ⇒ `ℕ) , `ℕ

