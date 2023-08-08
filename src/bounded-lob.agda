open import Shim
open import Cat.Cartesian
open import Presheaf as _
open import Functor.LaxMonoidalSemicomonad
module bounded-lob
  {l m n}
  (C : CartesianCat l m n)
  (F : LaxMonoidalSemicomonad l m n C)
  where

private module C = CartesianCat C
private module □ = LaxMonoidalSemicomonad F
open import Presheaf.Hom C.cat
open C
open □ using () renaming (run to □ ; cojoin to quot)

module setup
  {p} (Pred : C.Obj -> Type p)
  (Σ* : ∀ c -> Pred c -> C.Obj)
  (X : C.Obj)
  (is-short : Pred (□ X))
  {vs} (is-very-short : 𝟙 ~> X -> Type vs)
  {vvs} (is-very-very-short : 𝟙 ~> X -> Type vvs)
  {vvvs} (is-very-very-very-short : ∀ {a} -> (𝟙 ~> a) -> Type vvvs)
  (reflect : ∃[ t ∈ 𝟙 ~> X ] is-very-short t -> 𝟙 ~> Σ* (□ X) is-short)
  where

  import loopy C (∙~> X) as loopy
  private module loopy-setup = loopy.setup is-very-short (Σ* (□ X) is-short) reflect
  open loopy-setup public using (Fixpoint ; module notations)

  module conditions₁
    (s : C.Obj) -- s ~ Σ* (□(s ~> X)) λ{ m -> Π[ s₀ : 𝟙 ~> s ] ((s₀ ⨾ m) ⟫ is-short) }
    (pack : ∃[ f ∈ s ~> X ] ((s₀ : 𝟙 ~> s) -> is-very-very-very-short s₀ -> is-very-very-short (s₀ ⨾ f)) -> 𝟙 ~> s)
    (qual : ∀ ((t ▷ p) : ∃[ t ∈ s ~> X ] ((s₀ : 𝟙 ~> s) -> is-very-very-very-short s₀ -> is-very-very-short (s₀ ⨾ t))) -> is-very-short (pack (t ▷ p) ⨾ t))
    where

    P : s ~> X -> Type (m ⊔ vvs ⊔ vvvs)
    P f = ∀ (s₀ : 𝟙 ~> s) -> is-very-very-very-short s₀ -> is-very-very-short (s₀ ⨾ f)

    private module loopy-conditions₁ = loopy-setup.conditions₁ s P pack qual
    open loopy-conditions₁ public using (introspect)

    module conditions₂
      (key : s ~> Σ* (□ X) is-short)
      (key-law : ∀ {(t ▷ p) : ∃[ t ∈ s ~> X ] P t} -> (pack (t ▷ p) ⨾ key) ≈ reflect (introspect (t ▷ p)))

      (f : Σ* (□ X) is-short ~> X)
      where

      private module loopy-conditions₂ = loopy-conditions₁.conditions₂ key key-law f
      open loopy-conditions₂ public using (t)

      module theorem
        (p : P t)
        where

        private module loopy-theorem = loopy-conditions₂.theorem p
        open loopy-theorem public using (fixpt)
