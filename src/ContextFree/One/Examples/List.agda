module ContextFree.One.Examples.List where

open import ContextFree.One.Desc
open import ContextFree.One.DescFunction
open import ContextFree.One.Unquoting (quote Desc) (quote μ) (quote RawIsContextFree)
open import ContextFree.One.Quoted
open import ContextFree.One.Quoting
open import Data.Fin using (#_)
open import Data.Unit.Base
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

infixr 5 _∷_

data ListP (A : Set) : Set where
  [] : ListP A
  _∷_ : A → ListP A → ListP A

desc : (A : Set) → Desc
desc A = `1 `+ (`P₀ A `* `var `* `1) `+ `0

to : (A : Set) → ListP A → μ (desc A)
to A [] = ⟨ inj₁ tt ⟩
to A (x ∷ xs) = ⟨ inj₂ (inj₁ (x , to A xs , tt)) ⟩

from : (A : Set) → μ (desc A) → ListP A
from A ⟨ inj₁ tt ⟩ = []
from A ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = x ∷ from A xs
from A ⟨ inj₂ (inj₂ ()) ⟩

to-from : (A : Set) → ∀ x → from A (to A x) ≡ x
to-from A [] = refl
to-from A (x ∷ xs) = cong (_∷_ x) (to-from A xs)

from-to : (A : Set) → ∀ x → to A (from A x) ≡ x
from-to A ⟨ inj₁ tt ⟩ = refl
from-to A ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = cong (λ v → ⟨ inj₂ (inj₁ (x , v , tt)) ⟩) (from-to A xs)
from-to A ⟨ inj₂ (inj₂ ()) ⟩

isContextFree-ListP : ∀ A → IsContextFree (ListP A)
isContextFree-ListP A = record { desc = desc A ; to = to A ; from = from A
                               ; to-from = to-from A ; from-to = from-to A }

qdt : NamedSafeDatatype
qdt = quoteDatatype! (quote ListP) 1

module TestQdt where
  open import Reflection
  open import Data.List
  testQdt : NamedSafeDatatype.sop qdt ≡ (quote ListP.[]  , []) ∷
                                        (quote ListP._∷_ , Spar (# 0) ∷ Srec ∷ []) ∷
                                        []
  testQdt = refl

qdesc : DescFun (proj₁ (unnameSafeDatatype qdt))
qdesc = descFun (proj₁ (unnameSafeDatatype qdt))
unquoteDecl qto = makeTo qto (quote qdesc) qdt
unquoteDecl qfrom = makeFrom qfrom (quote qdesc) qdt
unquoteDecl qcf = makeRecord (quote qdesc) (quote qto) (quote qfrom) qdt

testDesc : ∀{A} → qdesc A ≡ desc A
testDesc = refl

testTo : ∀{A} xs → qto A xs ≡ to A xs
testTo [] = refl
testTo (x ∷ xs) = cong (λ v → ⟨ inj₂ (inj₁ (x , v , tt)) ⟩) (testTo xs)

testFrom : ∀{A} xs → qfrom A xs ≡ from A xs
testFrom ⟨ inj₁ tt ⟩ = refl
testFrom ⟨ inj₂ (inj₁ (x , xs , tt)) ⟩ = cong (_∷_ x) (testFrom xs)
testFrom ⟨ inj₂ (inj₂ ()) ⟩
