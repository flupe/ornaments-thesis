module Cx.Extended.Examples where

open import Common
open import Cx.Cx.Core
open import Cx.Extended.Desc
open import Cx.Extended.Ornament

natD : DatDesc ε ε 2
natD = ι (const tt)
       ⊕ rec (const tt) ⊗ ι (const tt)
       ⊕ `0

natD-zero : μ natD tt tt
natD-zero = ⟨ 0 , refl ⟩
natD-suc : μ natD tt tt → μ natD tt tt
natD-suc n = ⟨ 1 , n , refl ⟩

listD : DatDesc ε (ε ▷₁ const Set) 2
listD = ι (λ _ → tt)
      ⊕ top ⊗ rec (const tt) ⊗ ι (const tt)
      ⊕ `0

`nil : ∀{A} → μ listD (tt , A) tt
`nil = ⟨ 0 , refl ⟩

`cons : ∀{A} → A → μ listD (tt , A) tt → μ listD (tt , A) tt
`cons x xs = ⟨ 1 , x , xs , refl ⟩

vecD : DatDesc (ε ▷ const Nat) (ε ▷₁ const Set) 2
vecD = ι (const (tt , 0))
     ⊕ const Nat ⊗ top ∘ pop ⊗ rec (λ γ → tt , top₀ (pop₀ γ)) ⊗ ι (λ γ → tt , suc (top (pop γ)))
     ⊕ `0

module NatToList where
  -- Index stays ε. Parameters become (ε ▷₁ const Set).
  nat→list : Orn ε id (ε ▷₁ const Set) (const tt) natD
  nat→list = ι (λ δ → inv tt)
           ⊕ top +⊗ rec (λ δ → inv tt) ⊗ ι (λ δ → inv tt)
           ⊕ `0

  test-nat→list : ornToDesc nat→list ≡ listD
  test-nat→list = refl

module ListToNatList where
  list-ex : μ listD (tt , Nat) tt
  list-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

  list→natlist : Orn ε id ε ((_, Nat)) listD
  list→natlist = ι (λ _ → inv tt)
               ⊕ -⊗ rec (λ _ → inv tt) ⊗ ι (λ _ → inv tt)
               ⊕ `0

  natlist-ex : μ (ornToDesc list→natlist) tt tt
  natlist-ex = ⟨ 1 , 100 , ⟨ 1 , 33 , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

module ListToVec where
  list→vec : Orn (ε ▷ const Nat) (const tt) (ε ▷₁ const Set) id listD
  list→vec = ι (const (inv (tt , zero)))
           ⊕  const Nat +⊗ -⊗ rec inv ∘ (λ δ → tt , top (pop δ)) ⊗ ι (λ δ → inv (tt , suc (top (pop δ))))
           ⊕ `0

  test-list→vec : ornToDesc list→vec ≡ vecD
  test-list→vec = refl

open import Cx.Extended.AlgebraicOrnament

module LengthAlgebra where
  lengthAlg : ∀ {A} → Alg listD (tt , A) (λ tt → Nat)
  lengthAlg (zero , refl) = 0
  lengthAlg (suc zero , x , xs , refl) = suc xs
  lengthAlg (suc (suc ()) , _)

  list→vec : Orn (ε ▷ const Nat) (const tt) (ε ▷₁ const Set) id listD
  list→vec = algOrn listD lengthAlg

  vecD′ : DatDesc (ε ▷ const Nat) (ε ▷₁ const Set) 2
  vecD′ = ι (λ _ → (tt , 0))
        ⊕ top ⊗ (λ _ → Nat) ⊗ rec (λ γ → tt , top γ) ⊗ ι (λ γ → tt , suc (top γ))
        ⊕ `0

  test-list→vec : ornToDesc list→vec ≡ vecD′
  test-list→vec = refl

module ReornamentNatToList where
  open NatToList

  nat→vec : Orn (ε ▷ const (μ natD tt tt)) (const tt) (ε ▷₁ const Set) (const tt) natD
  nat→vec = reornament nat→list

  vecD′ : DatDesc (ε ▷ const (μ natD tt tt)) (ε ▷₁ const Set) 2
  vecD′ = ι (λ _ → (tt , natD-zero))
        ⊕ top ⊗ (λ _ → μ natD tt tt) ⊗ rec (λ γ → tt , top γ) ⊗ ι (λ γ → tt , natD-suc (top γ))
        ⊕ `0

  test-nat→vec : ornToDesc nat→vec ≡ vecD′
  test-nat→vec = refl

  ex-vec : μ (ornToDesc nat→vec) (tt , Nat) (tt , (natD-suc (natD-suc natD-zero)))
  ex-vec = ⟨ 1 , 33 , _ , ⟨ 1 , 44 , _ , ⟨ 0 , refl ⟩ , refl ⟩ , refl ⟩

  test-forget-vec : forget nat→vec ex-vec ≡ natD-suc (natD-suc natD-zero)
  test-forget-vec = refl
