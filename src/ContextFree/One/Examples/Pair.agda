module ContextFree.One.Examples.Pair where

open import ContextFree.One.Desc
open import ContextFree.One.Quoting
open import ContextFree.One.Quoted
open import ContextFree.One.Unquoting (quote Desc) (quote μ)
open import Data.Unit.Base
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

data Pair (A B : Set) : Set where
  pair : (a : A) → (b : B) → Pair A B

desc : (A B : Set) → Desc
desc A B = `K A `* `K B `* `1 `+ `0

to : (A B : Set) → Pair A B → μ (desc A B)
to A B (pair a b) = ⟨ inj₁ (a , b , tt) ⟩

from : (A B : Set) → μ (desc A B) → Pair A B
from A B ⟨ inj₁ (a , b , tt) ⟩ = pair a b
from A B ⟨ inj₂ () ⟩

to-from : (A B : Set) → ∀ x → from A B (to A B x) ≡ x
to-from A B (pair a b) = refl

from-to : (A B : Set) → ∀ x → to A B (from A B x) ≡ x
from-to A B ⟨ inj₁ (a , b , tt) ⟩ = refl
from-to A B ⟨ inj₂ () ⟩

isContextFree-Pair : ∀ A B → IsContextFree (Pair A B)
isContextFree-Pair A B = record { desc = desc A B ; to = to A B ; from = from A B
                                ; to-from = to-from A B ; from-to = from-to A B }

qdt : SafeDatatype
qdt = quoteDatatype! (quote Pair) 2

unquoteDecl qdesc = makeDesc qdt
unquoteDecl qto = makeTo (quote qdesc) qto qdt

testDesc : ∀{A B} → qdesc A B ≡ desc A B
testDesc = refl

testTo : ∀{A B} x → qto A B x ≡ to A B x
testTo (pair a b) = refl
