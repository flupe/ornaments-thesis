module Cx.Test where

open import Common
open import Reflect
open import Cx.HasDesc
open import Cx.Quoting
open import Cx.Unquoting

open HasDesc using (desc)

data ℕ : Set where
  ze : ℕ
  su : (n : ℕ) → ℕ

data 𝔹 : Set where
  tt ff : 𝔹

unquoteDecl quotedℕ HasDescℕ = deriveHasDesc quotedℕ HasDescℕ (quote ℕ)
unquoteDecl quoted𝔹 HasDesc𝔹 = deriveHasDesc quoted𝔹 HasDesc𝔹 (quote 𝔹)

ℕ→list : Orn ε _ (ε ▷₁ const Set) _ (desc HasDescℕ)
ℕ→list = ι (λ _ → inv tt)
       ⊕ "x" / top +⊗ "xs" /rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt) 
       ⊕ `0

list→vec = reornament ℕ→list

𝔹→maybe : Orn ε _ (ε ▷₁ const Set) _ (desc HasDesc𝔹)
𝔹→maybe = "x" / top +⊗ ι (λ δ → inv tt)
        ⊕ ι (λ δ → inv tt)
        ⊕ `0

listD : DatDesc ε (ε ▷₁ const Set) 2
listD = ornToDesc ℕ→list

vecD : DatDesc (ε ▷ const (μ (desc HasDescℕ) tt tt)) (ε ▷₁ const Set) 2
vecD = ornToDesc list→vec

maybeD : DatDesc ε (ε ▷₁ const Set) 2
maybeD = ornToDesc 𝔹→maybe

data mabe (A : Set) : unquoteDat maybeD where
  juss : unquoteCon maybeD 0 mabe
  noth : unquoteCon maybeD 1 mabe

data liss (A : Set) : unquoteDat listD where
  naught : unquoteCon listD 0 liss
  conss  : unquoteCon listD 1 liss

data vek (A : Set) : unquoteDat vecD where
  naught : unquoteCon vecD 0 vek
  conss  : unquoteCon vecD 1 vek
