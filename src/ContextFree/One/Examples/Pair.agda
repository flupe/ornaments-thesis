module ContextFree.One.Examples.Pair where

open import Common
open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.EmbeddingProjection
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting

data Pair (A B : Set) : Set where
  pair : (a : A) → (b : B) → Pair A B

desc : (A B : Set) → Desc
desc A B = `P₀ A `* `P₀ B `* `1 `+ `0

pattern α a b = pair a b
pattern β a b = ⟨ left (a , b , tt) ⟩
pattern absurd-β = ⟨ right () ⟩

to : (A B : Set) → Pair A B → μ (desc A B)
to A B (α a b) = β a b

from : (A B : Set) → μ (desc A B) → Pair A B
from A B (β a b) = α a b
from A B absurd-β

to-from : (A B : Set) → ∀ x → from A B (to A B x) ≡ x
to-from A B (α a b) = refl

from-to : (A B : Set) → ∀ x → to A B (from A B x) ≡ x
from-to A B (β a b) = refl
from-to A B absurd-β

isContextFree-Pair : ∀ A B → IsContextFree (Pair A B)
isContextFree-Pair A B = record { desc = desc A B ; to = to A B ; from = from A B
                                ; to-from = to-from A B ; from-to = from-to A B }

qdt : NamedSafeDatatype
qdt = quoteDatatypeᵐ Pair

module TestQdt where
  open import Builtin.Reflection
  open import ContextFree.One.Params
  test-qdt : qdt ≡ mk (quote Pair) 2 (param₀ visible "A" ∷ param₀ visible "B" ∷ [])
                      ((quote pair , Spar 1 ∷ Spar 0 ∷ []) ∷
                       [])
  test-qdt = refl

unquoteDecl qrec = defineRecord qrec qdt

module Q (A B : Set) = RawIsContextFree (qrec A B)

testDesc : ∀{A B} → Q.desc A B ≡ desc A B
testDesc = refl

testTo : ∀{A B} x → Q.to A B x ≡ to A B x
testTo (α a b) = refl

testFrom : ∀{A B} x → Q.from A B x ≡ from A B x
testFrom (β a b) = refl
testFrom absurd-β
