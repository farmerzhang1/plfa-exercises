module agda.part1.induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym) -- congruence
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩ -- !!!wow
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎ -- if we only use ≡⟨⟩ refl can be used I guess
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- +-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- +-assoc′ zero    n p                          =  refl
-- +-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Building proofs interactively

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm m (n + p) | +-comm m p | +-assoc n p m = refl

+-distribute : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
+-distribute zero n p = refl
+-distribute (suc m) n p rewrite +-distribute m n p | +-assoc p (m * p) (n * p) = refl

+-massoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
+-massoc zero n p = refl
+-massoc (suc m) n p rewrite +-distribute n (m * n) p | +-massoc m n p = refl

+-zz : ∀ (m : ℕ) →  m * zero ≡ zero * m 
+-zz zero = refl
+-zz (suc m) rewrite +-zz m = refl

+-getone : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n
+-getone zero n = refl
+-getone (suc m) n rewrite +-getone m n | +-swap n m (m * n) = refl

+-mcomm : ∀ (m n : ℕ) → m * n ≡ n * m
+-mcomm m zero rewrite +-zz m = refl
+-mcomm m (suc n) rewrite +-getone m n | +-mcomm m n = refl

+-mionus : ∀ (n : ℕ) → zero ∸ n ≡ zero
+-mionus zero = refl
+-mionus (suc n) = refl -- why???

∸-|-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-|-assoc zero n p rewrite +-mionus n | +-mionus (n + p) | +-mionus p = refl
∸-|-assoc (suc m) zero p = refl
∸-|-assoc (suc m) (suc n) p rewrite ∸-|-assoc m n p = refl

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identity′ (m ^ p) = refl
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p 
                                 | +-massoc m (m ^ n) (m ^ p) = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p 
                              | +-massoc m n ((m ^ p) * (n ^ p)) 
                              | +-massoc m (m ^ p) (n * (n ^ p)) = {!   !}

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n p = {!   !} -- 不写了！