open import Shim
module Cat l m n where

record Cat : Type (lsuc (l ⊔ m ⊔ n)) where

  field Obj : Type l

  field _~>_ : Obj -> Obj -> Type m
  infix 1 _~>_

  field _≈_ : ∀ {a1 a2} -> (a1 ~> a2) -> (a1 ~> a2) -> Type n
  infix 1 _≈_

  field ι₂ : ∀ {a1 a2} {f : a1 ~> a2} -> (f ≈ f)
  field ÷₂_ : ∀ {a1 a2} {f1 f2 : a1 ~> a2} -> (f1 ≈ f2) -> (f2 ≈ f1)
  infix 12 ÷₂_
  field _⨾₂_ : ∀ {a1 a2} {f1 f2 f3 : a1 ~> a2} -> (f1 ≈ f2) -> (f2 ≈ f3) -> (f1 ≈ f3)
  infixl 9 _⨾₂_

  field ι : ∀ {a} -> (a ~> a)
  field ι′ : ∀ {a} -> (ι ≈ ι {a})

  field _⨾_ : ∀ {a1 a2 a3} -> (a1 ~> a2) -> (a2 ~> a3) -> (a1 ~> a3)
  infixl 9 _⨾_
  field
    _⨾′_ : ∀ {a1 a2 a3} -> {f1 f2 : a1 ~> a2} -> (f1 ≈ f2) -> {g1 g2 : a2 ~> a3} -> (g1 ≈ g2) -> ((f1 ⨾ g1) ≈ (f2 ⨾ g2))
  infixl 9 _⨾′_

  _^⨾′_ : ∀ {a1 a2 a3} -> (f : a1 ~> a2) -> {g1 g2 : a2 ~> a3} -> (g1 ≈ g2) -> ((f ⨾ g1) ≈ (f ⨾ g2))
  f ^⨾′ q = ι₂ ⨾′ q
  infixr 9 _^⨾′_

  _⨾′^_ : ∀ {a1 a2 a3} -> {f1 f2 : a1 ~> a2} -> (f1 ≈ f2) -> (g : a2 ~> a3) -> ((f1 ⨾ g) ≈ (f2 ⨾ g))
  p ⨾′^ g = p ⨾′ ι₂
  infixl 9 _⨾′^_

  _^⨾′^_ : ∀ {a1 a2 a3} -> (f : a1 ~> a2) -> (g : a2 ~> a3) -> ((f ⨾ g) ≈ (f ⨾ g))
  f ^⨾′^ g = ι₂ ⨾′ ι₂
  infixl 9 _^⨾′^_

  field ι⨾ : ∀ {a1 a2} {f : a1 ~> a2} -> (ι ⨾ f) ≈ f
  field ⨾ι : ∀ {a1 a2} {f : a1 ~> a2} -> (f ⨾ ι) ≈ f
  field ⨾⨾ : ∀ {a1 a2 a3 a4} {f : a1 ~> a2} {g : a2 ~> a3} {h : a3 ~> a4} -> (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h)
