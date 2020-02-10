module Cx.Quoting where

open import Reflect
open import Common
open import Cx.Named public
open import Cx.Quoting.Constructor
open import Cx.Quoting.QuotedDesc public

quoteConstructors : (`dt : Name) (#p : Nat) → ∀ I Γ → (cnames : List Name) →
                    TC (DatDesc I Γ (length cnames))
quoteConstructors `dt #p I Γ [] = return `0
quoteConstructors `dt #p I Γ (cname ∷ cnames) = do
  c  ← quoteConstructor `dt #p I Γ cname
  cs ← quoteConstructors `dt #p I Γ cnames
  return (c ⊕ cs)

quoteDatatype : (`dt : Name) → TC QuotedDesc
quoteDatatype `dt = do
  (getType `dt) bind λ dttype →
    (getParameters `dt) bind λ #p → 
      (typeToCx #p nothing dttype) bind λ I → 
        (typeToCx 0 (just #p) dttype) bind λ Γ →
          (getConstructors `dt) bind λ `cnames →
            (quoteConstructors `dt #p I Γ `cnames) bind λ datdesc →
              return (mk `dt (listToVec `cnames) datdesc)
  where _bind_ = bindTC

private
  tcEq : ∀{a}{A : Set a} → (x y : A) → TC (x ≡ y)
  tcEq x y = catchTC (unquoteTC (con₀ (quote _≡_.refl))) $
    quoteTC x >>=′ λ `x → quoteTC y >>=′ λ `y →
    typeError (strErr "tcEq:" ∷ termErr `x ∷
               strErr "does not equal" ∷ termErr `y ∷ [])

-- Connect a Desc to an existing datatype
-- quoteDatatype, decide if quoted desc is equal to given desc,
-- replace quoted desc by given desc
quoteDatatypeExisting : (`dt : Name) → ∀{I Γ #c} → DatDesc I Γ #c → TC QuotedDesc
quoteDatatypeExisting `dt {I} {Γ} {#c} D = do
  dw ← quoteDatatype `dt
  bindTC (tcEq I (QuotedDesc.I dw)) λ Ieq →
    bindTC (tcEq Γ (QuotedDesc.Γ dw)) λ Γeq →
      bindTC (tcEq #c (QuotedDesc.#c dw)) λ #ceq → 
        let D′ = transport id (DatDesc $≡ Ieq *≡ Γeq *≡ #ceq) D in
        bindTC (tcEq (toExtended D′) (toExtended (QuotedDesc.desc dw))) λ _ →
          return (mk (QuotedDesc.`datatypeName dw) (QuotedDesc.`constructorNames dw) D′)
  where open import Cx.Conversions
        open Extended↔Named
