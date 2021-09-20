module plfa.part1.Naturals where -- should be the same as the file path

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ -- love the Unicode!

{-# BUILTIN NATURAL ℕ #-}
seven : ℕ
seven = suc(suc(suc(suc(suc(suc(suc(zero)))))))

six : ℕ
six = 6 -- 好耶！

_+_ : ℕ → ℕ → ℕ -- Unicodes are hard to type!!
zero + n = n
suc (m) + n = suc(m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

infixl 6  _+_
infixl 7  _*_

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

aa : 2 + 4 ≡ 6
aa = refl


data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

el : Bin
el = ⟨⟩ I O I I

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (a O) = a I
inc (a I) = (inc a) O

to   : ℕ → Bin
from : Bin → ℕ

to zero = ⟨⟩
to (suc n) = inc (to n)

from (z O) = 2 * (from z)
from (o I) = 2 * (from o) + 1
from ⟨⟩ = zero