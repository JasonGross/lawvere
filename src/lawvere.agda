open import Shim
open import Cat.Cartesian
open CartesianClosedCat using (cat)
module lawvere
  {l m n}
  (C : CartesianClosedCat l m n)
  where

private module C = CartesianClosedCat C
open C
import lawvere-without-cartesian-closure C.ccat as lawvere

module setup
  (a : C.Obj)

  (s : C.Obj)

  (σ : s ~> (a ^ s))
  (σ⁻¹ : (s ~> a) -> (𝟙 ~> s))

  (f : a ~> a)
  where

  private module lawvere-setup = lawvere.setup a s ((σ ×× ι) ⨾ apply) σ⁻¹ f
  open lawvere-setup public using (Fixpoint ; introspect ; module notations)
  open notations

  module conditions
    (σ-point-surjection : ∀ {f g} -> (dup ⨾ (((σ⁻¹ f ⨾ σ) ×× g) ⨾ apply)) ≈ (g ⨾ f))
    where

    σ-point-surjection-alt : ∀ {f g} -> (dup ⨾ ((σ⁻¹ f ×× g) ⨾ ((σ ×× ι) ⨾ apply))) ≈ (g ⨾ f)
    σ-point-surjection-alt {f} {g}
      = (dup ⨾ ((σ⁻¹ f ×× g) ⨾ ((σ ×× ι) ⨾ apply))) =[ _ ^⨾′ ⨾⨾ ]=
     ⨾₂ (dup ⨾ (((σ⁻¹ f ×× g) ⨾ (σ ×× ι)) ⨾ apply)) =[ _ ^⨾′ (××⨾ ⨾′^ _) ]=
     ⨾₂ (dup ⨾ (((σ⁻¹ f ⨾ σ) ×× (g ⨾ ι)) ⨾ apply))  =[ _ ^⨾′ ((_ ^××′ ⨾ι) ⨾′^ _) ]=
     ⨾₂ (dup ⨾ (((σ⁻¹ f ⨾ σ) ×× g) ⨾ apply))        =[ σ-point-surjection ]=
     ⨾₂ (g ⨾ f)                                      [■]

    private module lawvere-conditions = lawvere-setup.conditions σ-point-surjection-alt
    open lawvere-conditions public using (t ; fixpt)
