open import Shim
open import Cat
open import Cat.Cartesian
open CartesianCat using (cat)
module no-presheaf
  {l m n}
  (C : CartesianCat l m n)
  where

open import Presheaf.Hom (C .cat)
private module C = CartesianCat C
open C

module setup
  (a : C.Obj)
  {q} (Q : 𝟙 ~> a → Type q)
  where

  import loopy C (∙~> a) as loopy
  private module loopy-setup = loopy.setup Q a fst
  open loopy-setup public using (Fixpoint ; module notations)

  module conditions₁
    (s : C.Obj)
    {p} (P : s ~> a → Type p)

    (pack : ∃[ t ∈ s ~> a ] P t → 𝟙 ~> s)
    (qual : ∀ ((t ▷ p) : ∃[ t ∈ s ~> a ] P t) → Q (pack (t ▷ p) ⨾ t))
    where

    private module loopy-conditions₁ = loopy-setup.conditions₁ s P pack qual
    open loopy-conditions₁ public using (introspect)

    module conditions₂
      (key : s ~> a)
      (key-law : ∀ {(t ▷ p) : ∃[ t ∈ s ~> a ] P t} → (pack (t ▷ p) ⨾ key) ≈ fst (introspect (t ▷ p)))

      (f : a ~> a)
      where

      private module loopy-conditions₂ = loopy-conditions₁.conditions₂ key key-law f
      open loopy-conditions₂ public using (t)

      module theorem
        (p : P t)
        where

        private module loopy-theorem = loopy-conditions₂.theorem p
        open loopy-theorem public using (fixpt)
