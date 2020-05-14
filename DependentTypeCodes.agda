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
data _⊢_  : Module → Term → Set

interp : ∀ {A} {Γ : Module} → Γ ⊢ A → Set

data Term where
  U    : Term
  #   : ℕ → Term
  Π    : Term → Term → Term

data Module where
 [] : Module
 _,⟨_,_∶_⟩ : (Γ : Module)
     → (A : Term)
     → (⊢A : Γ ⊢ A )
     → interp ⊢A
     → Module


infixl 5 _∋_

data _∋_ : Module → Term → Set where
  Z : ∀ {Γ A} {⊢A : Γ ⊢ A} {a : interp ⊢A}
    ---------
    → (Γ ,⟨ A ,  ⊢A ∶ a ⟩) ∋ A

  S_ : ∀ {Γ A B} {⊢B : Γ ⊢ B} {b : interp ⊢B}
     → Γ ∋ A
     ---------
     → Γ ,⟨ B , ⊢B ∶ b ⟩ ∋ A

toNum : ∀ {Γ t} → Γ ∋ t → ℕ
toNum Z =  0
toNum (S x) =  suc (toNum x)

-- Analogous to TypeCodes
data _⊢_ where

  `# : ∀ {Γ}
     → (i : Γ ∋ U)
     → Γ ⊢ # (toNum i)

  `U : ∀ {Γ}
     ----------
     → Γ ⊢ U

  `Π : ∀ {Γ F G}
     → (⊢F : Γ ⊢ F)
     → (f : interp ⊢F)
     → (⊢G : (Γ ,⟨ F , ⊢F ∶ f ⟩) ⊢ G)
     → Γ ⊢ Π F G
     {-
     The rule above isn't quite right because f need not be a concrete term
     because it should be provided as a parameter to the type under application.
     There needs to be a separate context that holds these locally bound
     variables.
     -}





lookup : Module → ℕ → Term
lookup [] n =  ⊥-elim impossible
  where postulate impossible : ⊥
lookup (Γ ,⟨ A , ⊢A ∶ x ⟩) F.0F = {!!}
lookup (Γ ,⟨ A , ⊢A ∶ x ⟩) (suc n) = {!!}

-- interp : ∀ {A} {Γ : Module} → Γ ⊢ A → Set
interp `U =  Set
interp (`# (Z {⊢A = `U} {a})) = a
interp (`# (S n)) =  interp (`# n)
interp (`Π F f G) = {! !}

--------------------------------------------------------------------------------
-------------------------------- Examples --------------------------------------
--------------------------------------------------------------------------------



ex : Module
ex = [] ,⟨  U    , `U       ∶ Bool  ⟩
        ,⟨  # 0  , `# Z     ∶ true  ⟩
        ,⟨  # 1  , `# (S Z) ∶ false ⟩
        ,⟨ U     , `U       ∶ ℕ    ⟩
        ,⟨ # 0   , `# Z     ∶ zero  ⟩

