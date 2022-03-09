module Duploid.Functor where

open import Preduploid
open import Duploid
import Preduploid.Functor as PF

open import Level

record Functor {o₁ ℓ₁ o₂ ℓ₂} (𝒞 : Duploid o₁ ℓ₁) (𝒟 : Duploid o₂ ℓ₂)
  : Set (levelOfTerm 𝒞 ⊔ levelOfTerm 𝒟) where
  private
    module 𝒞 = Duploid.Duploid 𝒞
    module 𝒟 = Duploid.Duploid 𝒟

  open 𝒟

  field
    F : PF.Functor 𝒞.𝒟 𝒟.𝒟

  open PF.Functor F

  field
    F-wrap-Thunkable : forall {N : 𝒞.Ob ⊝} -> Linear (F₁ (𝒞.wrap {N = N}))
    F-force-Linear : forall {P : 𝒞.Ob +} -> Linear (F₁ (𝒞.force {P = P}))
