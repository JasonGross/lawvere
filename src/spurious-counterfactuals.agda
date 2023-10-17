open import Shim
open import Cat.Cartesian
open import Presheaf as _
open import Functor.LaxMonoidalSemicomonad
module spurious-counterfactuals
  {l m n}
  (C : CartesianCat l m n)
  (F : LaxMonoidalSemicomonad l m n C)
  where

private module C = CartesianCat C
private module □ = LaxMonoidalSemicomonad F
open import Presheaf.Hom C.cat
open C hiding (Obj)
open □ using () renaming (run to □ ; cojoin to quot)

module setup
  {p} (Pred : C.Obj -> Type p)
  (Σ* : ∀ c -> Pred c -> C.Obj)
  (act : C.Obj)
  {g} (isgood : 𝟙 ~> act -> Type g)
  (qisgood : Pred (□ act))
  (reflect : ∃[ a ∈ 𝟙 ~> act ] isgood a -> 𝟙 ~> Σ* (□ act) qisgood)
  where

  import loopy C (∙~> act) as loopy
  private module loopy-setup = loopy.setup isgood (Σ* (□ act) qisgood) reflect
  open loopy-setup public using (Fixpoint ; module notations)

  module conditions₁
    (s : C.Obj) -- s ~ Σ* (□(s ~> act)) λ{ m -> Π[ s₀ : 𝟙 ~> s ] ((s₀ ⨾ m) ⟫ qisgood) }
    (pack : ∃[ f ∈ (s ~> act) ] ((s₀ : 𝟙 ~> s) -> isgood (s₀ ⨾ f)) -> 𝟙 ~> s)
    (qual : ∀ ((t ▷ p) : ∃[ f ∈ (s ~> act) ] ((s₀ : 𝟙 ~> s) -> isgood (s₀ ⨾ f))) -> isgood (pack (t ▷ p) ⨾ t))
    where

    P : s ~> act -> Type (m ⊔ g)
    P f = ∀ (s₀ : 𝟙 ~> s) -> isgood (s₀ ⨾ f)

    private module loopy-conditions₁ = loopy-setup.conditions₁ s P pack qual
    open loopy-conditions₁ public using (introspect)

    module conditions₂
      (key : s ~> Σ* (□ act) qisgood)
      (key-law : ∀ {(t ▷ p) : ∃[ t ∈ (s ~> act) ] P t} -> (pack (t ▷ p) ⨾ key) ≈ reflect (introspect (t ▷ p)))
      (f : Σ* (□ act) qisgood ~> act)
      where

      private module loopy-conditions₂ = loopy-conditions₁.conditions₂ key key-law f
      open loopy-conditions₂ public using (t)

      module theorem
        (p : P t)
        where

        private module loopy-theorem = loopy-conditions₂.theorem p
        open loopy-theorem public using (fixpt)
