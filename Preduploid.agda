module Preduploid where

open import Relation.Unary using (Pred)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Level

data Polarity : Set where
  + : Polarity
  ⊝ : Polarity

private
  variable p q r s : Polarity

record Preduploid o ℓ : Set (suc (o ⊔ ℓ)) where
  infix 4 _⇒_
  infix 9 _∙_ _∘_ _⊙_

  field
    Ob : Polarity -> Set o
    _⇒_ : REL (Ob p) (Ob q) ℓ

    id : forall {A : Ob p} -> A ⇒ A
    _∙_ : forall {A : Ob p} {B : Ob +} {C : Ob q} -> B ⇒ C -> A ⇒ B -> A ⇒ C
    _∘_ : forall {A : Ob p} {B : Ob ⊝} {C : Ob q} -> B ⇒ C -> A ⇒ B -> A ⇒ C

    identity∙ˡ : forall {A : Ob p} {B : Ob +} {f : A ⇒ B} -> id ∙ f ≡ f
    identity∙ʳ : forall {A : Ob +} {B : Ob p} {f : A ⇒ B} -> f ∙ id ≡ f

    identity∘ˡ : forall {A : Ob p} {B : Ob ⊝} {f : A ⇒ B} -> id ∘ f ≡ f
    identity∘ʳ : forall {A : Ob ⊝} {B : Ob p} {f : A ⇒ B} -> f ∘ id ≡ f

    assoc∙∙ : forall {A : Ob p} {B : Ob +} {C : Ob +} {D : Ob q}
      {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} -> (h ∙ g) ∙ f ≡ h ∙ (g ∙ f)
    assoc∘∘ : forall {A : Ob p} {B : Ob ⊝} {C : Ob ⊝} {D : Ob q}
      {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} -> (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)
    assoc∙∘ : forall {A : Ob p} {B : Ob ⊝} {C : Ob +} {D : Ob q}
      {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} -> (h ∙ g) ∘ f ≡ h ∙ (g ∘ f)

  π : Ob p -> Polarity
  π {p = p} _ = p

  _⊙_ : forall {A : Ob p} {B : Ob q} {C : Ob r} -> B ⇒ C -> A ⇒ B -> A ⇒ C
  _⊙_ {q = +} = _∙_
  _⊙_ {q = ⊝} = _∘_

  identityˡ : forall {A : Ob p} {B : Ob q} {f : A ⇒ B} -> id ⊙ f ≡ f
  identityˡ {q = +} = identity∙ˡ
  identityˡ {q = ⊝} = identity∘ˡ

  identityʳ : forall {A : Ob p} {B : Ob q} {f : A ⇒ B} -> f ⊙ id ≡ f
  identityʳ {p = +} = identity∙ʳ
  identityʳ {p = ⊝} = identity∘ʳ

  Linear : forall {C : Ob r} {D : Ob s} -> Pred (C ⇒ D) (o ⊔ ℓ)
  Linear {C = C} {D = D} f = forall {p q} {A : Ob p} {B : Ob q} {g : B ⇒ C} {h : A ⇒ B} -> f ⊙ (g ⊙ h) ≡ (f ⊙ g) ⊙ h

  Thunkable : forall {A : Ob p} {B : Ob q} -> Pred (A ⇒ B) (o ⊔ ℓ)
  Thunkable {A = A} {B = B} f = forall {r s} {C : Ob r} {D : Ob s} {g : B ⇒ C} {h : C ⇒ D} -> h ⊙ (g ⊙ f) ≡ (h ⊙ g) ⊙ f

  P-Linear : forall {P : Ob +} {A : Ob p} -> (f : P ⇒ A) -> Linear f
  P-Linear f {q = +} = sym assoc∙∙
  P-Linear f {q = ⊝} = sym assoc∙∘

  N-Thunkable : forall {A : Ob p} {N : Ob ⊝} -> (f : A ⇒ N) -> Thunkable f
  N-Thunkable f {r = +} = sym assoc∙∘
  N-Thunkable f {r = ⊝} = sym assoc∘∘

