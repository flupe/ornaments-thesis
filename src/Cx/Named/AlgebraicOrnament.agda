
module Cx.Named.AlgebraicOrnament where

open import Common
open import Cx.Named.Ornament public


----------------------------------------
-- Algebraic ornament

module _ {I : Cx}{J : Pow ⟦ I ⟧} where
  -- Interestingly, algebraic ornaments only work when the Algebra is
  -- polymorphic in the datatype parameters. That is because during the
  -- definition of datatypes we do not know the values of the parameters, and
  -- by extension we do not know them in an ornament.
  algOrn : ∀{Γ Δ dt}{c : Cxf Δ Γ}(D : Desc I Γ dt) →
           (∀{δ : ⟦ Δ ⟧} → Alg D (c δ) J) → DefOrn (I ▷ J) pop Δ c D
  algOrn {dt = isCon} {c = c} (ι o) α = ι (λ δ → inv (o (c δ) , α refl))
  algOrn {dt = isCon} (nm / S ⊗ xs) α = nm /-⊗ (algOrn xs (λ {γ} → curry α (top γ)))
  algOrn {dt = isCon} {c = c} (nm /rec i ⊗ xs) α = "_" / (J ∘ i ∘ c)
                                                +⊗ nm /rec (λ δ → inv (i (c $ pop δ) , top δ))
                                                 ⊗ algOrn xs (λ {δ} → curry α (top δ))
  algOrn {dt = isDat _} `0 α = `0
  algOrn {dt = isDat _} (x ⊕ xs) α = algOrn x (curry α 0) ⊕ algOrn xs (α ∘ (suc *** id))


----------------------------------------
-- Composition of ornaments

module _ {I J K}{u : Cxf J I}{v : Cxf K J} where
  infixl 9 _>>⁺_
  _>>⁺_ : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
            (o : Orn u c D) → Orn v d (ornToDesc o) → Orn (u ∘ v) (c ∘ d) D
  _>>⁺_ (ι j) (ι k) = ι (λ _ → inv-∘ (j _) (k _))
  _>>⁺_ (ι j) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (ι j) ys⁺)
  _>>⁺_ (ι j) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (ι j) ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (nm /-⊗ ys⁺) = nm /-⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ /-⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (nm /rec j +⊗ ys⁺) = nm /rec j +⊗ (_>>⁺_ (nm′ /-⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /-⊗ xs⁺) (give-K t ys⁺) = give-K t (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ /rec j ⊗ xs⁺) (nm /rec k ⊗ ys⁺) = nm /rec (λ _ → inv-∘ (j _) (k _)) ⊗ _>>⁺_ xs⁺ ys⁺
  _>>⁺_ (nm′ /rec j ⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ /rec j ⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /rec j ⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (nm′ /rec j ⊗ xs⁺) ys⁺)
  _>>⁺_ {d = d} (nm′ / S +⊗ xs⁺) (nm /-⊗ ys⁺) = nm / (S ∘ d) +⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ / S +⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ / S +⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ / S +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (nm′ / S +⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ / S +⊗ xs⁺) (give-K t ys⁺) = _>>⁺_ xs⁺ ys⁺
  _>>⁺_ (nm′ /rec j +⊗ xs⁺) (nm /rec k ⊗ ys⁺) = nm /rec (uninv ∘ k) +⊗ (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ (nm′ /rec j +⊗ xs⁺) (nm / T +⊗ ys⁺) = nm / T +⊗ (_>>⁺_ (nm′ /rec j +⊗ xs⁺) ys⁺)
  _>>⁺_ (nm′ /rec j +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = nm /rec k +⊗ (_>>⁺_ (nm′ /rec j +⊗ xs⁺) ys⁺)
  _>>⁺_ {d = d} (give-K s xs⁺) ys⁺ = give-K (s ∘ d) (_>>⁺_ xs⁺ ys⁺)
  _>>⁺_ `0 `0 = `0
  _>>⁺_ (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = (_>>⁺_ x⁺ y⁺) ⊕ (_>>⁺_ xs⁺ ys⁺)

  -- To prove that composition is sound we show that the right description is
  -- returned. The descriptions contain higher order terms so we use
  -- extensionality to compare them.
  module _ (ext : ∀{a b} → Extensionality a b) where
    >>⁺-sound : ∀{Γ Δ Δ′ dt}{c : Cxf Δ Γ}{d : Cxf Δ′ Δ} {D : Desc I Γ dt} →
                    (o : Orn u c D) → (p : Orn v d (ornToDesc o)) →
                    (ornToDesc (o >>⁺ p)) ≡ ornToDesc p
    >>⁺-sound {d = d} (ι j) (ι k) = cong ι (ext (λ x → uninv-inv-∘ (j (d x)) (k x)))
    >>⁺-sound (ι {i = i} {c} j) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-sound (ι {i = i} {c} j) ys⁺)
    >>⁺-sound (ι {i = i} {c} j) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-sound (ι {i = i} {c} j) ys⁺)
    >>⁺-sound (nm′ /-⊗ xs⁺) (nm /-⊗ ys⁺) = cong (_/_⊗_ _ _) (>>⁺-sound xs⁺ ys⁺)
    >>⁺-sound (nm′ /-⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-sound (nm′ /-⊗ xs⁺) ys⁺)
    >>⁺-sound (nm′ /-⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-sound (nm′ /-⊗ xs⁺) ys⁺)
    >>⁺-sound (nm′ /-⊗ xs⁺) (give-K t ys⁺) = >>⁺-sound xs⁺ ys⁺
    >>⁺-sound {d = d} (nm′ /rec j ⊗ xs⁺) (nm /rec k ⊗ ys⁺) =
      cong₂ (_/rec_⊗_ _) (ext (λ x → uninv-inv-∘ (j (d x)) (k x))) (>>⁺-sound xs⁺ ys⁺)
    >>⁺-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) ys⁺)
    >>⁺-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-sound (_/rec_⊗_ {i = i} nm′ j xs⁺) ys⁺)
    >>⁺-sound {d = d} (nm′ / S +⊗ xs⁺) (nm /-⊗ ys⁺) = cong (_/_⊗_ nm (S ∘ d)) (>>⁺-sound xs⁺ ys⁺)
    >>⁺-sound (nm′ / S +⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-sound (nm′ / S +⊗ xs⁺) ys⁺)
    >>⁺-sound (nm′ / S +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-sound (nm′ / S +⊗ xs⁺) ys⁺)
    >>⁺-sound (nm′ / S +⊗ xs⁺) (give-K t ys⁺) = >>⁺-sound xs⁺ ys⁺
    >>⁺-sound (nm′ /rec j +⊗ xs⁺) (nm /rec k ⊗ ys⁺) = cong (_/rec_⊗_ nm (uninv ∘ k)) (>>⁺-sound xs⁺ ys⁺)
    >>⁺-sound (nm′ /rec j +⊗ xs⁺) (nm / T +⊗ ys⁺) = cong (_/_⊗_ nm T) (>>⁺-sound (nm′ /rec j +⊗ xs⁺) ys⁺)
    >>⁺-sound (nm′ /rec j +⊗ xs⁺) (nm /rec k +⊗ ys⁺) = cong (_/rec_⊗_ nm k) (>>⁺-sound (nm′ /rec j +⊗ xs⁺) ys⁺)
    >>⁺-sound (give-K s xs⁺) ys⁺ = >>⁺-sound xs⁺ ys⁺
    >>⁺-sound `0 `0 = refl
    >>⁺-sound (x⁺ ⊕ xs⁺) (y⁺ ⊕ ys⁺) = cong₂ _⊕_ (>>⁺-sound x⁺ y⁺) (>>⁺-sound xs⁺ ys⁺)


----------------------------------------
-- Reornaments currently only work when the original datatype does not have
-- parameters. To make it work for all datatypes, the indices have to be
-- dependent on the parameters. (See handwritten notes)

reornament : ∀{I J Δ}{u : Cxf J I}{c : Cxf Δ ε}{#c}{D : DatDesc I ε #c} →
             (o : Orn u c D) → Orn (u ∘ pop) c D
reornament o = o >>⁺ algOrn (ornToDesc o) (λ {δ} → forgetAlg o {δ})
