open import Shim
open import Cat.Cartesian
open CartesianCat using (cat)
module lawvere-without-cartesian-closure
  {l m n}
  (C : CartesianCat l m n)
  where

open import Presheaf.Hom (C .cat)
private module C = CartesianCat C
open C hiding (Obj)

module setup
  (a : C.Obj)

  (s : C.Obj)

  (σ : (s × s) ~> a)
  (σ⁻¹ : (s ~> a) -> (𝟙 ~> s))

  (f : a ~> a)
  where

  import singleton C (∙~> a) as loopy-singleton
  private module loopy-setup = loopy-singleton.setup a (λ{ x -> x }) s σ⁻¹
  open loopy-setup public using (Fixpoint ; introspect ; module notations)
  open notations

  module conditions
    (σ-point-surjection : ∀ {f g} -> (dup ⨾ ((σ⁻¹ f ×× g) ⨾ σ)) ≈ (g ⨾ f))
    where

    key : s ~> a
    key = dup ⨾ σ

    key-law : ∀ {t : s ~> a} -> (σ⁻¹ t ⨾ (dup ⨾ σ)) ≈ (σ⁻¹ t ⨾ t)
    key-law {t} = (σ⁻¹ t ⨾ (dup ⨾ σ))            =[ ⨾⨾ ]=
               ⨾₂ ((σ⁻¹ t ⨾ dup) ⨾ σ)            =[ dup⨾ ⨾′^ _ ]=
               ⨾₂ ((dup ⨾ (σ⁻¹ t ×× σ⁻¹ t)) ⨾ σ) =[ ÷₂ ⨾⨾ ]=
               ⨾₂ (dup ⨾ ((σ⁻¹ t ×× σ⁻¹ t) ⨾ σ)) =[ σ-point-surjection ]=
               ⨾₂ (σ⁻¹ t ⨾ t)                     [■]

    module loopy-conditions = loopy-setup.conditions key key-law f
    open loopy-conditions public using (t ; fixpt)
