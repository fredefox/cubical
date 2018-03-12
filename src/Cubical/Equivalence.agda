module Cubical.Equivalence where

open import Cubical.FromStdLib
open import Cubical.Primitives using (_≡_)
open import Cubical.NType public using (isContr)

fiber : ∀ {ℓ ℓ'} {E : Set ℓ} {B : Set ℓ'} (f : E → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {E = E} f y = Σ[ x ∈ E ] y ≡ f x

module _ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') where
  isEquiv : (A → B) → Set (ℓ-max ℓ ℓ')
  isEquiv f = (y : B) → isContr (fiber f y)

{-# BUILTIN ISEQUIV isEquiv #-}

module _ {ℓa ℓb : Level} (A : Set ℓa) (B : Set ℓb) where
  private
    ℓ = ℓ-max ℓa ℓb

  record AreInverses (f : A → B) (g : B → A) : Set ℓ where
    field
      verso-recto : g ∘ f ≡ idFun A
      recto-verso : f ∘ g ≡ idFun B

  Isomorphism : (f : A → B) → Set _
  Isomorphism f = Σ (B → A) λ g → AreInverses f g

  _≅_ : Set ℓ
  _≅_ = Σ _ Isomorphism

  record _≃_ : Set ℓ where
    no-eta-equality
    constructor con
    field
      eqv : A → B
      isEqv : isEquiv A B eqv

    -- FIXME I wanna replace the field with named `eqv` with this.
    obverse : A → B
    obverse = eqv

    inverse : B → A
    inverse b = fst (fst (isEqv b))

    -- We can extract an isomorphism from an equivalence.
    --
    -- One way to do it would be to use univalence and coersion - but there's
    -- probably a more straight-forward way that does not require breaking the
    -- dependency graph between this module and Cubical.Univalence
    areInverses : AreInverses obverse inverse
    areInverses = record
      { verso-recto = verso-recto
      ; recto-verso = recto-verso
      }
      where
      postulate
        verso-recto : inverse ∘ obverse ≡ idFun A
        recto-verso : obverse ∘ inverse ≡ idFun B

    toIsomorphism : _≅_
    toIsomorphism = obverse , (inverse , areInverses)

    open AreInverses areInverses public
