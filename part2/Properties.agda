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

-- extending the map
ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)           =  ⊢` (ρ ∋w)
-- use the previous lemma to extend the map ρ suitably and use induction to rename the body of the abstraction.
rename ρ (⊢ƛ ⊢N)           =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)         =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero             =  ⊢zero
rename ρ (⊢suc ⊢M)         =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)  = ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)           =  ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z) = ⊥-elim (x≢x refl)
  ρ (S x≢z (S x₁≢z z)) = S x₁≢z z

swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z = S x≢y Z
  ρ (S x≢y Z) = Z
  ρ (S x≢z (S z≢y n)) = S z≢y (S x≢z n)

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
{- 这个是x := 的那个 -} {- 这个x是 x ⦂ 的那个 -} -- 可以{ x = y } 这样就可以省略不想要的implicit argument
subst {x = y} ⊢V (⊢` {x = x}  Z) with x ≟ y
... | yes _           = weaken ⊢V
... | no  x≢y         = ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        = ⊥-elim (x≢y refl)
... | no  _           = ⊢` ∋x
subst ⊢V (⊢L · ⊢M)    = (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero        = ⊢zero
subst ⊢V (⊢suc ⊢M)    = ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        = ⊢ƛ (drop ⊢N)
... | no  x≢y         = ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl        = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y         = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl        = ⊢μ (drop ⊢M)
... | no  x≢y         = ⊢μ (subst ⊢V (swap x≢y ⊢M))

{-
Rewrite subst to work with the modified definition _[_:=_]′
from the exercise in the previous chapter.
As before, this should factor dealing with
bound variables into a single function,
defined by mutual recursion
with the proof that substitution preserves types.
-}
drop-or-swap : ∀ {V Γ N A B C}
  → ∅ ⊢ V ⦂ A
  → (x : Id) → (y : Id)
  → Γ , y ⦂ A , x ⦂ C ⊢ N ⦂ B
  → Γ , x ⦂ C ⊢ N [ y := V ]′if x ≢ y ⦂ B

subst′ : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ]′ ⦂ B
subst′ {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _           = weaken ⊢V
... | no  x≢y         = ⊥-elim (x≢y refl)
subst′ {x = y} ⊢V (⊢` {x = x} (S x≢y Γ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no _ = ⊢` Γ∋x
subst′ {x = y} ⊢V (⊢ƛ {x = x} ⊢N) = ⊢ƛ (drop-or-swap ⊢V x y ⊢N)
subst′ ⊢V (⊢L · ⊢M) = (subst′ ⊢V ⊢L) · (subst′ ⊢V ⊢M)
subst′ ⊢V ⊢zero = ⊢zero
subst′ ⊢V (⊢suc ⊢N) = ⊢suc (subst′ ⊢V ⊢N)
subst′ {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) = ⊢case (subst′ ⊢V ⊢L) (subst′ ⊢V ⊢M) (drop-or-swap ⊢V x y ⊢N)
subst′ {x = y} ⊢V (⊢μ {x = x} ⊢N) = ⊢μ (drop-or-swap ⊢V x y ⊢N)

drop-or-swap ⊢V x y ⊢N with x ≟ y
... | yes refl = drop ⊢N
... | no  x≢y = subst′ ⊢V (swap x≢y ⊢N)

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where

  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L                                =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin

_ : eval (gas 100) (⊢twoᶜ · ⊢sucᶜ · ⊢zero) ≡
  steps
   ((ƛ "s" ⇒ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z"))) · (ƛ "n" ⇒ `suc ` "n")
   · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · ` "z")) ·
     `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ "n" ⇒ `suc ` "n") · ((ƛ "n" ⇒ `suc ` "n") · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "n" ⇒ `suc ` "n") · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl

_ : eval (gas 100) ⊢2+2 ≡
  steps
  ((μ "+" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
  · `suc (`suc `zero)
  · `suc (`suc `zero)
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒
    (ƛ "n" ⇒
    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
        (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
      · ` "m"
      · ` "n")
    ]))
  · `suc (`suc `zero)
  · `suc (`suc `zero)
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒
    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
    · ` "m"
    · ` "n")
    ])
  · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
    · ` "m"
    · `suc (`suc `zero))
  ]
  —→⟨ β-suc (V-suc V-zero) ⟩
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
    · `suc `zero
    · `suc (`suc `zero))
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  `suc
  ((ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
        (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
      · ` "m"
      · ` "n")
      ]))
    · `suc `zero
    · `suc (`suc `zero))
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  `suc
  ((ƛ "n" ⇒
    case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
        (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
      · ` "m"
      · ` "n")
    ])
    · `suc (`suc `zero))
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
  `suc
  case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
  `suc
  ((μ "+" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
      ])))
    · ` "m"
    · `suc (`suc `zero))
  ]
  —→⟨ ξ-suc (β-suc V-zero) ⟩
  `suc
  (`suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
    · `zero
    · `suc (`suc `zero)))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  `suc
  (`suc
    ((ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
          (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
        · ` "m"
        · ` "n")
      ]))
    · `zero
    · `suc (`suc `zero)))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
  `suc
  (`suc
    ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒
      `suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
        (ƛ "n" ⇒
          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
          ])))
      · ` "m"
      · ` "n")
      ])
    · `suc (`suc `zero)))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  `suc
  (`suc
    case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
    `suc
    ((μ "+" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
        ])))
    · ` "m"
    · `suc (`suc `zero))
    ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl
aa : eval (gas 100) ⊢2-2 ≡
  steps
  ((μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · `suc (`suc `zero)
  · `suc (`suc `zero)
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒
    (ƛ "n" ⇒
    case ` "m" [zero⇒ `zero |suc "m" ⇒
    case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒
    (μ "-" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ `zero |suc "m" ⇒
        case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
        ])))
    · ` "m"
    · ` "n"
    ]
    ]))
  · `suc (`suc `zero)
  · `suc (`suc `zero)
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  (ƛ "n" ⇒
    case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
    case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒
    (μ "-" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
    · ` "m"
    · ` "n"
    ]
    ])
  · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
  case `suc (`suc `zero) [zero⇒ `suc ` "m" |suc "n" ⇒
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · ` "m"
  · ` "n"
  ]
  ]
  —→⟨ β-suc (V-suc V-zero) ⟩
  case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "n" ⇒
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · `suc `zero
  · ` "n"
  ]
  —→⟨ β-suc (V-suc V-zero) ⟩
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · `suc `zero
  · `suc `zero
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒
    (ƛ "n" ⇒
    case ` "m" [zero⇒ `zero |suc "m" ⇒
    case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒
    (μ "-" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ `zero |suc "m" ⇒
        case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
        ])))
    · ` "m"
    · ` "n"
    ]
    ]))
  · `suc `zero
  · `suc `zero
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
  (ƛ "n" ⇒
    case `suc `zero [zero⇒ `zero |suc "m" ⇒
    case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒
    (μ "-" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
    · ` "m"
    · ` "n"
    ]
    ])
  · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
  case `suc `zero [zero⇒ `zero |suc "m" ⇒
  case `suc `zero [zero⇒ `suc ` "m" |suc "n" ⇒
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · ` "m"
  · ` "n"
  ]
  ]
  —→⟨ β-suc V-zero ⟩
  case `suc `zero [zero⇒ `suc `zero |suc "n" ⇒
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · `zero
  · ` "n"
  ]
  —→⟨ β-suc V-zero ⟩
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · `zero
  · `zero
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  (ƛ "m" ⇒
    (ƛ "n" ⇒
    case ` "m" [zero⇒ `zero |suc "m" ⇒
    case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒
    (μ "-" ⇒
      (ƛ "m" ⇒
      (ƛ "n" ⇒
        case ` "m" [zero⇒ `zero |suc "m" ⇒
        case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
        ])))
    · ` "m"
    · ` "n"
    ]
    ]))
  · `zero
  · `zero
  —→⟨ ξ-·₁ (β-ƛ V-zero) ⟩
  (ƛ "n" ⇒
    case `zero [zero⇒ `zero |suc "m" ⇒
    case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒
    (μ "-" ⇒
    (ƛ "m" ⇒
      (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
    · ` "m"
    · ` "n"
    ]
    ])
  · `zero
  —→⟨ β-ƛ V-zero ⟩
  case `zero [zero⇒ `zero |suc "m" ⇒
  case `zero [zero⇒ `suc ` "m" |suc "n" ⇒
  (μ "-" ⇒
    (ƛ "m" ⇒
    (ƛ "n" ⇒
      case ` "m" [zero⇒ `zero |suc "m" ⇒
      case ` "n" [zero⇒ `suc ` "m" |suc "n" ⇒ ` "-" · ` "m" · ` "n" ]
      ])))
  · ` "m"
  · ` "n"
  ]
  ]
  —→⟨ β-zero ⟩ `zero ∎)
  (done V-zero)
aa = refl

Normal : Term → Set
Normal M  =  ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M  =  Normal M × ¬ Value M

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck {M} {A} ⊢M ⟨ fst , snd ⟩ with progress ⊢M
... | step x = fst x
... | done x = snd x

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N -- many steps of reductions
    ---------
  → ∅ ⊢ N ⦂ A
preserves {M} {N} {A} ⊢M M—↠N with M—↠N
... | M ∎ = ⊢M
... | M —→⟨ x₁ ⟩ y with progress ⊢M
... | step _ = preserves (preserve ⊢M x₁) y -- one step of reduction
... | done x = ⊥-elim (V¬—→ x x₁)

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs ⊢M m2n = unstuck (preserves ⊢M m2n)

-- i get stuck ()
stuck : ∀ {A} → ¬ (∅ ⊢ ` "x" ⦂ A) → Stuck (` "x")
stuck {A} ¬M = ⟨ normalx , ¬valuex ⟩ where
  normalx : Normal (` "x")
  normalx ()
  ¬valuex : ¬ Value (` "x")
  ¬valuex ()
-- i get unstuck!

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl
