module QEC where

open import Data.Nat
open import Data.Vec

data Pauli : Set where
  I : Pauli
  X : Pauli
  Y : Pauli
  Z : Pauli

PauliOperator : ℕ → Set
PauliOperator = Vec Pauli

_⋅_ : Pauli → Pauli → Pauli
_ ⋅ I = I
I ⋅ _ = I
X ⋅ X = I
X ⋅ Y = Z
X ⋅ Z = Y
Y ⋅ X = Z
Y ⋅ Y = I
Y ⋅ Z = X
Z ⋅ X = Y
Z ⋅ Y = X
Z ⋅ Z = I

_•_ : {n : ℕ} → PauliOperator n → PauliOperator n → PauliOperator n
_•_ = zipWith _⋅_
