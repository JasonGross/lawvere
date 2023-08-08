open import Shim
open import Cat
open import Cat.Cartesian
open import Presheaf as _
open CartesianClosedCat using (cat)
module lawvere
  {l m n}
  (C : CartesianClosedCat l m n)
  where

open import Presheaf.Hom (C .cat)
private module C = CartesianClosedCat C
open C

module setup
  (a : C.Obj)

  (s : C.Obj)

  (σ : s ~> (a ^ s))
  (σ⁻¹ : (s ~> a) -> (𝟙 ~> s))

  (f : a ~> a)
  where

  import singleton C.ccat (∙~> a) as loopy-singleton
  private module loopy-setup = loopy-singleton.setup a (λ{ x -> x }) s σ⁻¹
  open loopy-setup public using (Fixpoint ; introspect ; module notations)
  open notations

  module conditions
    (σ-point-surjection : ∀ {f g} -> (dup ⨾ (((σ⁻¹ f ⨾ σ) ×× g) ⨾ apply)) ≈ (g ⨾ f))
    where

    key : s ~> a
    key = dup ⨾ ((σ ×× ι) ⨾ apply)

    key-law : ∀ {t : s ~> a} -> (σ⁻¹ t ⨾ (dup ⨾ ((σ ×× ι) ⨾ apply))) ≈ (σ⁻¹ t ⨾ t)
    key-law {t} = (σ⁻¹ t ⨾ (dup ⨾ ((σ ×× ι) ⨾ apply)))            [ ⨾⨾ ]
               ⨾₂ ((σ⁻¹ t ⨾ dup) ⨾ ((σ ×× ι) ⨾ apply))            [ dup-natural ⨾′^ _ ]
               ⨾₂ ((dup ⨾ (σ⁻¹ t ×× σ⁻¹ t)) ⨾ ((σ ×× ι) ⨾ apply)) [ (÷₂ ⨾⨾) ⨾₂ (_ ^⨾′ ⨾⨾) ]
               ⨾₂ (dup ⨾ (((σ⁻¹ t ×× σ⁻¹ t) ⨾ (σ ×× ι)) ⨾ apply)) [ _ ^⨾′ (××-natural ⨾′^ _) ]
               ⨾₂ (dup ⨾ (((σ⁻¹ t ⨾ σ) ×× (σ⁻¹ t ⨾ ι)) ⨾ apply))  [ _ ^⨾′ ((_ ^××′ ⨾ι) ⨾′^ _) ]
               ⨾₂ (dup ⨾ ((((σ⁻¹ t ⨾ σ) ×× σ⁻¹ t)) ⨾ apply))      [ σ-point-surjection ]
               ⨾₂ (σ⁻¹ t ⨾ t)                                     [■]

    module loopy-conditions = loopy-setup.conditions key key-law f
    open loopy-conditions public using (t ; fixpt)
