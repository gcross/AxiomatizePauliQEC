module Pauli where

import Algebra.FunctionProperties
open import Data.Fin using (Fin; #_; suc; zero)
open import Data.Fin.Props using (eq?)
open import Function.LeftInverse as LeftInverse
open import Function.LeftInverse using (LeftInverse)
open import Relation.Binary.PropositionalEquality as P 
open import Relation.Nullary.Core using (Dec; yes; no)
import Decision

data Pauli : Set where
  I : Pauli
  X : Pauli
  Y : Pauli
  Z : Pauli

open Algebra.FunctionProperties {A = Pauli} _≡_ using (Commutative)

_⋅_ : Pauli → Pauli → Pauli
X ⋅ X = I
X ⋅ Y = Z
X ⋅ Z = Y
Y ⋅ X = Z
Y ⋅ Y = I
Y ⋅ Z = X
Z ⋅ X = Y
Z ⋅ Y = X
Z ⋅ Z = I
I ⋅ a = a
a ⋅ I = a

to : Pauli → Fin 4
to I = # 0
to X = # 1
to Y = # 2
to Z = # 3

from : Fin 4 → Pauli
from zero = I
from (suc zero) = X
from (suc (suc zero)) = Y
from (suc (suc (suc zero))) = Z
from (suc (suc (suc (suc ()))))

finite : LeftInverse (P.setoid Pauli) (P.setoid (Fin 4))
finite = record
  { to           = P.→-to-⟶ to
  ; from         = P.→-to-⟶ from
  ; left-inverse = from∘to
  }
  where
  from∘to : ∀ x → from (to x) ≡ x
  from∘to I = refl
  from∘to X = refl
  from∘to Y = refl
  from∘to Z = refl

open import Decision

fromYes : ∀ {P : Set} (x : Dec P) {p} → x ≡ yes p → P
fromYes .(yes p) {p} refl = p

⋅-left-identity :: LeftIdentity I _⋅_
⋅-left-identity = fromYes (\a → I ⋅ a) id
