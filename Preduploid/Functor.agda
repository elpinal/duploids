module Preduploid.Functor where

open import Preduploid

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Level

private
  variable p q r s : Polarity

record Functor {o₁ ℓ₁ o₂ ℓ₂} (𝒞 : Preduploid o₁ ℓ₁) (𝒟 : Preduploid o₂ ℓ₂)
  : Set (levelOfTerm 𝒞 ⊔ levelOfTerm 𝒟) where
  private
    module 𝒞 = Preduploid.Preduploid 𝒞
    module 𝒟 = Preduploid.Preduploid 𝒟

  open 𝒟

  field
    F₀ : 𝒞.Ob p -> Ob p
    F₁ : forall {A : 𝒞.Ob p} {B : 𝒞.Ob q} -> A 𝒞.⇒ B -> F₀ A ⇒ F₀ B

    identity : forall {A : 𝒞.Ob p} -> F₁ 𝒞.id ≡ id {A = F₀ A}
    homomorphism : forall {A : 𝒞.Ob p} {B : 𝒞.Ob q} {C : 𝒞.Ob r} {f : A 𝒞.⇒ B} {g : B 𝒞.⇒ C}
      -> F₁ (g 𝒞.⊙ f) ≡ F₁ g ⊙ F₁ f
