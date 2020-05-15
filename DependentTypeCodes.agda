{-# OPTIONS --type-in-type #-}

module DependentTypeCodes where

open import Data.Nat using (ℕ ; suc ; zero ; _<_ ; z≤n ; s≤s)
import Data.Fin as F
open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (Σ-syntax) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_)


infixl 9 _,⟨_,_∶_⟩


data Term : Set
data Module : Set
data Context (Γ : Module) : Set
data _∣_⊢_  : (Γ : Module) → Context Γ → Term → Set
_⊢_ : Module → Term → Set

data EvalContext {Γ} : Context Γ → Set

interp : ∀ {A} {Γ : Module} {Δ : Context Γ} {δ : EvalContext Δ} → Γ ∣ Δ ⊢ A → Set

data Term where
  U    : Term
  #_   : ℕ → Term
  ♯_   : ℕ → Term
  Π    : Term → Term → Term

data Context Γ where
  ∅ : Context Γ
  _∷_ : ∀ {A} → (Δ : Context Γ) → Γ ∣ Δ ⊢ A → Context Γ

Γ ⊢ A = Γ ∣ ∅ ⊢ A


data EvalContext {Γ} where
  ∅ : EvalContext ∅
  _∷_ : ∀ {Δ A} {⊢A : Γ ∣ Δ ⊢ A}
      → (δ : EvalContext Δ)
      → interp {A} {Γ} {Δ} {δ} ⊢A
      → EvalContext (Δ ∷ ⊢A)



data Module where
 [] : Module
 _,⟨_,_∶_⟩ : (Γ : Module)
     → (A : Term)
     → (⊢A : Γ ⊢ A )
     → interp {δ = ∅} ⊢A
     → Module




infixl 5 _∋_
infixl 5 _∋ₗ_
infixl 4 _∣_⊢_

data _∋_ : Module → Term → Set where
  Z : ∀ {Γ A} {⊢A : Γ ⊢ A} {a : interp ⊢A}
    ---------
    → (Γ ,⟨ A ,  ⊢A ∶ a ⟩) ∋ A

  S_ : ∀ {Γ A B} {⊢B : Γ ⊢ B} {b : interp ⊢B}
     → Γ ∋ A
     ---------
     → Γ ,⟨ B , ⊢B ∶ b ⟩ ∋ A



data _∋ₗ_ {Γ : Module} : Context Γ → Term → Set where
  Z : ∀ {A} {Δ : Context Γ} {⊢A : Γ ∣ Δ ⊢ A}
    ----------------
    → ( Δ ∷ ⊢A) ∋ₗ A

  S_ : ∀ {Δ A B} {⊢B : Γ ∣ Δ ⊢ B}
     → Δ ∋ₗ A
     -----------------------------
     → Δ ∷ ⊢B ∋ₗ A

toNum : ∀ {Γ t} → Γ ∋ t → ℕ
toNum Z =  0
toNum (S x) =  suc (toNum x)

toNumₗ : ∀ {Γ t} {Δ : Context Γ} → Δ ∋ₗ t → ℕ
toNumₗ Z =  0
toNumₗ (S x) =  suc (toNumₗ x)

-- Analogous to TypeCodes
data _∣_⊢_ where

  -- Module-based variables
  `#_ : ∀ {Γ Δ}
     → (i : Γ ∋ U)
     → Γ ∣ Δ ⊢ # (toNum i)

  -- Context-based variables
  `♯_ : ∀ {Γ} {Δ : Context Γ}
      → (i : _∋ₗ_ {Γ} Δ U)
      → Γ ∣ Δ ⊢ ♯ (toNumₗ i)

  `U : ∀ {Γ Δ}
     ----------
     → Γ ∣ Δ ⊢ U

  `Π : ∀ {Γ Δ F G}
     → (⊢F : Γ ∣ Δ ⊢ F)
     → (⊢G : Γ ∣ Δ ∷ ⊢F ⊢ G)
     → Γ ∣ Δ ⊢ Π F G


--------------------------------------------------------------------------------
-------------------------------- Substituion -----------------------------------
--------------------------------------------------------------------------------

-- _[_] : ∀ {Γ A B} {Δ : Context Γ} {⊢B : Γ ∣ Δ ⊢ B}
--      → Γ ∣ Δ ∷ ⊢B ⊢ A
--      → Γ ∣ Δ ⊢ B
--      ----------
--      → Γ ∣ Δ ⊢ A
-- _[_] ⊢A ⊢B = {!!}

-- subst : ∀ {Γ Δ₁ Δ₂}
--       → (∀ {A} → Δ₁ ∋ₗ A → Γ ∣ Δ₂ ⊢ A)
--       -----------------------
--       → (∀ {A} → Γ ∣ Δ₁ ⊢ A → Γ ∣ Δ₂ ⊢ A)
-- subst ρ ⊢A = {!!}

--------------------------------------------------------------------------------
------------------------------ Interpretation ----------------------------------
--------------------------------------------------------------------------------
lookup : ∀ {Γ} → (i : Γ ∋ U) → Set

lookupₗ : ∀ {Γ} {Δ : Context Γ} {δ : EvalContext Δ} → (i : Δ ∋ₗ U) → Set

-- interpEC : ∀ {A} {Γ : Module} {Δ : Context Γ} (δ : EvalContext Δ) → Γ ∣ Δ ⊢ A → Set

-- interp : ∀ {A} {Γ : Module} {Δ : Context Γ} {δ : EvalContext Δ} → Γ ∣ Δ ⊢ A → Set
interp `U                      =  Set
interp (`# i)                  =  lookup i
interp {δ = δ} (`Π F G)        =  (x : interp {δ = δ} F) →  interp {δ =  δ ∷ x} G
interp {δ = δ} (`♯ i)          =  lookupₗ {δ = δ} i


-- interpEC (_∷_ {⊢A = `U} δ x) (`♯ (Z {⊢A = .`U})) = x
-- {-# CATCHALL #-}
-- interpEC (δ ∷ x) (`♯ (S i)) =  interpEC δ (`♯ i)
-- {-# CATCHALL #-}
-- interpEC δ ⊢A =  interp ⊢A


lookup {Γ ,⟨ .U , `U ∶ x ⟩} Z =  x
{-# CATCHALL #-}
lookup {Γ ,⟨ A , ⊢A ∶ x ⟩} (S i) =  lookup i


lookupₗ {δ = _∷_ {⊢A = `U} δ x} (Z {⊢A = .`U}) = x
{-# CATCHALL #-}
lookupₗ {δ = δ ∷ x} (S i) =  lookupₗ {δ = δ} i

--------------------------------------------------------------------------------
-------------------------------- Examples --------------------------------------
--------------------------------------------------------------------------------

id : (A : Set) → A → A
id A x = x

ex : Module
ex = [] ,⟨  U    , `U       ∶ Bool  ⟩
        ,⟨  # 0  , `# Z     ∶ true  ⟩
        ,⟨  # 1  , `# (S Z) ∶ false ⟩
        ,⟨ U     , `U       ∶ ℕ    ⟩
        ,⟨ # 0   , `# Z     ∶ zero  ⟩
        ,⟨  Π (# 1) (# 1)   ,  `Π ( `# ( S Z)) ( `# ( S Z) ) ∶  (Data.Nat._+_ 1)  ⟩
        ,⟨  Π U U ,  `Π  `U  `U ∶ ( λ x → x) ⟩
        -- ,⟨  Π U (Π (♯ 0) (♯ 1)) ,  `Π  `U  ( `Π {!!} {!!}) ∶ id ⟩

ex2 : Module
ex2 = [] ,⟨  Π U (Π (♯ 0) (♯ 1)) ,  `Π  `U  ( `Π (`♯ Z) (`♯ S Z)) ∶ id ⟩

