module Duploid where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning

open import Level

open import Preduploid

private
  variable p q r s : Polarity

record Duploid o ℓ : Set (suc (o ⊔ ℓ)) where
  field
    𝒟 : Preduploid o ℓ

  open Preduploid.Preduploid 𝒟 public

  field
    ⇓ : Ob ⊝ -> Ob +
    ⇑ : Ob + -> Ob ⊝

    delay : forall {P : Ob +} -> P ⇒ ⇑ P
    force : forall {P : Ob +} -> ⇑ P ⇒ P

    wrap : forall {N : Ob ⊝} -> N ⇒ ⇓ N
    unwrap : forall {N : Ob ⊝} -> ⇓ N ⇒ N

    force∘delay∙ : forall {A : Ob p} {P : Ob +} {f : A ⇒ P} -> force ∘ (delay ∙ f) ≡ f
    ∘unwrap∙wrap : forall {N : Ob ⊝} {A : Ob p} {f : N ⇒ A} -> (f ∘ unwrap) ∙ wrap ≡ f
    delay∙force : forall {P : Ob +} -> delay ∙ force ≡ id {A = ⇑ P}
    wrap∘unwrap : forall {N : Ob ⊝} -> wrap ∘ unwrap ≡ id {A = ⇓ N}

  ∙force∘delay : forall {P : Ob +} {A : Ob p} {g : P ⇒ A} -> (g ∙ force) ∘ delay ≡ g
  ∙force∘delay {g = g} =
    begin
      (g ∙ force) ∘ delay
    ≡⟨ assoc∙∘ ⟩
      g ∙ (force ∘ delay)
    ≡˘⟨ cong (g ∙_) (cong (force ∘_) identity∙ʳ) ⟩
      g ∙ (force ∘ (delay ∙ id))
    ≡⟨ cong (g ∙_) force∘delay∙ ⟩
      g ∙ id
    ≡⟨ identity∙ʳ ⟩
     g
    ∎

  unwrap∙wrap∘ : forall {A : Ob p} {N : Ob ⊝} {g : A ⇒ N} -> unwrap ∙ (wrap ∘ g) ≡ g
  unwrap∙wrap∘ {g = g} =
    begin
      unwrap ∙ (wrap ∘ g)
    ≡˘⟨ assoc∙∘ ⟩
      (unwrap ∙ wrap) ∘ g
    ≡˘⟨ cong (_∘ g) (cong (_∙ wrap) identity∘ˡ) ⟩
      ((id ∘ unwrap) ∙ wrap) ∘ g
    ≡⟨ cong (_∘ g) ∘unwrap∙wrap ⟩
      id ∘ g
    ≡⟨ identity∘ˡ ⟩
      g
    ∎

  wrap-Thunkable : forall {N : Ob ⊝} -> Thunkable (wrap {N = N})
  wrap-Thunkable {r = +} = sym assoc∙∙
  wrap-Thunkable {r = ⊝} {g = g} {h = h} =
    begin
      h ∘ (g ∙ wrap)
    ≡˘⟨ ∘unwrap∙wrap ⟩
      ((h ∘ (g ∙ wrap)) ∘ unwrap) ∙ wrap
    ≡⟨ cong (_∙ wrap) assoc∘∘ ⟩
      (h ∘ ((g ∙ wrap) ∘ unwrap)) ∙ wrap
    ≡⟨ cong (_∙ wrap) (cong (h ∘_) assoc∙∘) ⟩
      (h ∘ (g ∙ (wrap ∘ unwrap))) ∙ wrap
    ≡⟨ cong (_∙ wrap) (cong (h ∘_) (cong (g ∙_) wrap∘unwrap)) ⟩
      (h ∘ (g ∙ id)) ∙ wrap
    ≡⟨ cong (_∙ wrap) (cong (h ∘_) identity∙ʳ) ⟩
      (h ∘ g) ∙ wrap
    ∎

  force-Linear : forall {P : Ob +} -> Linear (force {P = P})
  force-Linear {q = +} {g = g} {h = h} = sym (
    begin
      (force ∘ g) ∙ h
    ≡˘⟨ force∘delay∙ ⟩
      force ∘ (delay ∙ ((force ∘ g) ∙ h))
    ≡˘⟨ cong (force ∘_) assoc∙∙ ⟩
      force ∘ ((delay ∙ (force ∘ g)) ∙ h)
    ≡˘⟨ cong (force ∘_) (cong (_∙ h) assoc∙∘) ⟩
      force ∘ (((delay ∙ force) ∘ g) ∙ h)
    ≡⟨ cong (force ∘_) (cong (_∙ h) (cong (_∘ g) delay∙force)) ⟩
      force ∘ ((id ∘ g) ∙ h)
    ≡⟨ cong (force ∘_) (cong (_∙ h) identity∘ˡ) ⟩
      force ∘ (g ∙ h)
    ∎)
  force-Linear {q = ⊝} = sym assoc∘∘

  helper1 : forall {A : Ob p} {P : Ob +} {f : A ⇒ P}
    -> (wrap ∘ delay) ∙ f ≡ wrap ∘ (delay ∙ f)
    -> forall {B : Ob q} {h : ⇑ P ⇒ B} -> (h ∘ delay) ∙ f ≡ h ∘ (delay ∙ f)
  helper1 {f = f} e {h = h} =
    begin
      (h ∘ delay) ∙ f
    ≡˘⟨ cong (_∙ f) (cong (_∘ delay) ∘unwrap∙wrap) ⟩
      (((h ∘ unwrap) ∙ wrap) ∘ delay) ∙ f
    ≡⟨ cong (_∙ f) assoc∙∘ ⟩
      ((h ∘ unwrap) ∙ (wrap ∘ delay)) ∙ f
    ≡⟨ assoc∙∙ ⟩
      (h ∘ unwrap) ∙ ((wrap ∘ delay) ∙ f)
    ≡⟨ cong ((h ∘ unwrap) ∙_) e ⟩
      (h ∘ unwrap) ∙ (wrap ∘ (delay ∙ f))
    ≡˘⟨ assoc∙∘ ⟩
      ((h ∘ unwrap) ∙ wrap) ∘ (delay ∙ f)
    ≡⟨ cong (_∘ _) ∘unwrap∙wrap ⟩
      h ∘ (delay ∙ f)
    ∎

  assoc-wrap∘delay∙→Thunkable : forall {A : Ob p} {P : Ob +} {f : A ⇒ P}
    -> (wrap ∘ delay) ∙ f ≡ wrap ∘ (delay ∙ f)
    -> Thunkable f
  assoc-wrap∘delay∙→Thunkable e {r = +} = sym assoc∙∙
  assoc-wrap∘delay∙→Thunkable {f = f} e {r = ⊝} {g = g} {h = h} =
    begin
      h ∘ (g ∙ f)
    ≡˘⟨ cong (h ∘_) (cong (_∙ f) ∙force∘delay) ⟩
      h ∘ (((g ∙ force) ∘ delay) ∙ f)
    ≡⟨ cong (h ∘_) (helper1 e) ⟩
      h ∘ ((g ∙ force) ∘ (delay ∙ f))
    ≡˘⟨ assoc∘∘ ⟩
      (h ∘ (g ∙ force)) ∘ (delay ∙ f)
    ≡˘⟨ helper1 e ⟩
      ((h ∘ (g ∙ force)) ∘ delay) ∙ f
    ≡⟨ cong (_∙ f) assoc∘∘ ⟩
      (h ∘ ((g ∙ force) ∘ delay)) ∙ f
    ≡⟨ cong (_∙ f) (cong (h ∘_) ∙force∘delay) ⟩
      (h ∘ g) ∙ f
    ∎

  helper2 : forall {N : Ob ⊝} {A : Ob p} {f : N ⇒ A}
    -> f ∘ (unwrap ∙ force) ≡ (f ∘ unwrap) ∙ force
    -> forall {B : Ob q} {h : B ⇒ ⇓ N} -> f ∘ (unwrap ∙ h) ≡ (f ∘ unwrap) ∙ h
  helper2 {f = f} e {h = h} =
    begin
      f ∘ (unwrap ∙ h)
    ≡˘⟨ cong (f ∘_) (cong (unwrap ∙_) force∘delay∙) ⟩
      f ∘ (unwrap ∙ (force ∘ (delay ∙ h)))
    ≡˘⟨ cong (f ∘_) assoc∙∘ ⟩
      f ∘ ((unwrap ∙ force) ∘ (delay ∙ h))
    ≡˘⟨ assoc∘∘ ⟩
      (f ∘ (unwrap ∙ force)) ∘ (delay ∙ h)
    ≡⟨ cong (_∘ (delay ∙ h)) e ⟩
      ((f ∘ unwrap) ∙ force) ∘ (delay ∙ h)
    ≡⟨ assoc∙∘ ⟩
      (f ∘ unwrap) ∙ (force ∘ (delay ∙ h))
    ≡⟨ cong ((f ∘ unwrap) ∙_) force∘delay∙ ⟩
      (f ∘ unwrap) ∙ h
    ∎

  assoc-∘unwrap∙force→Linear : forall {N : Ob ⊝} {A : Ob p} {f : N ⇒ A}
    -> f ∘ (unwrap ∙ force) ≡ (f ∘ unwrap) ∙ force
    -> Linear f
  assoc-∘unwrap∙force→Linear {f = f} e {q = +} {g = g} {h = h} =
    begin
      f ∘ (g ∙ h)
    ≡˘⟨ cong (f ∘_) (cong (_∙ h) unwrap∙wrap∘) ⟩
      f ∘ ((unwrap ∙ (wrap ∘ g)) ∙ h)
    ≡⟨ cong (f ∘_) assoc∙∙ ⟩
      f ∘ (unwrap ∙ ((wrap ∘ g) ∙ h))
    ≡⟨ helper2 e ⟩
      (f ∘ unwrap) ∙ ((wrap ∘ g) ∙ h)
    ≡˘⟨ assoc∙∙ ⟩
      ((f ∘ unwrap) ∙ (wrap ∘ g)) ∙ h
    ≡˘⟨ cong (_∙ h) assoc∙∘ ⟩
      (((f ∘ unwrap) ∙ wrap) ∘ g) ∙ h
    ≡⟨ cong (_∙ h) (cong (_∘ g) ∘unwrap∙wrap) ⟩
      (f ∘ g) ∙ h
    ∎
  assoc-∘unwrap∙force→Linear e {q = ⊝} = sym assoc∘∘
