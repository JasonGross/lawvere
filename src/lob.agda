open import Shim
open import Cat
open import Cat.Cartesian
open import Presheaf as _
open import Functor.LaxMonoidalSemicomonad
module lob
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
  (x : C.Obj)

  (s : C.Obj)

  (pack : (□ s ~> x) -> 𝟙 ~> □ s)
  where

  import singleton C (∙~> x) as loopy-singleton
  private module loopy-setup = loopy-singleton.setup (□ x) (λ{ f -> □.𝟙-codistr ⨾ □.map f }) (□ s) pack
  open loopy-setup public using (Fixpoint ; introspect)
  module notations where
    chain : ∀ {a1 a2} {f g : a1 ~> a2} -> f ≈ g -> f ≈ g
    chain x = x

    syntax chain {f = f} pf = f =[ pf ]=

    _[■] : ∀ {a1 a2} (f : a1 ~> a2) -> f ≈ f
    f [■] = ι₂
  open notations

  module conditions
    (unpack : (s × □ s) ~> x)
    (unpack-point-surjection : ∀ {f : □ s ~> x} {g : 𝟙 ~> □ (□ s)}
      -> (dup ⨾ ((pack f ×× g) ⨾ (□.×-codistr ⨾ □.map unpack))) ≈ (g ⨾ □.map f))
    (f : □ x ~> x)
    where

    key : □ s ~> □ x
    key = dup ⨾ ((ι ×× quot) ⨾ (□.×-codistr ⨾ □.map unpack))

    key-law : ∀ {t : □ s ~> x} -> (pack t ⨾ key) ≈ (□.𝟙-codistr ⨾ □.map (introspect t))
    key-law {t}
      = (pack t ⨾ (dup ⨾ ((ι ×× quot) ⨾ (□.×-codistr ⨾ □.map unpack))))             =[ ⨾⨾ ⨾₂ (dup⨾ ⨾′^ _) ⨾₂ (÷₂ ⨾⨾) ]=
     ⨾₂ (dup ⨾ ((pack t ×× pack t) ⨾ ((ι ×× quot) ⨾ (□.×-codistr ⨾ □.map unpack)))) =[ _ ^⨾′ (⨾⨾ ⨾₂ (××⨾ ⨾′^ _)) ]=
     ⨾₂ (dup ⨾ (((pack t ⨾ ι) ×× (pack t ⨾ quot)) ⨾ (□.×-codistr ⨾ □.map unpack)))  =[ _ ^⨾′ ((⨾ι ××′^ _) ⨾′^ _) ]=
     ⨾₂ (dup ⨾ ((pack t ×× (pack t ⨾ quot)) ⨾ (□.×-codistr ⨾ □.map unpack)))        =[ unpack-point-surjection ]=
     ⨾₂ ((pack t ⨾ quot) ⨾ □.map t)                =[ □.map-cojoin ⨾′^ _ ]=
     ⨾₂ ((□.𝟙-codistr ⨾ □.map (pack t)) ⨾ □.map t) =[ ÷₂ ⨾⨾ ]=
     ⨾₂ (□.𝟙-codistr ⨾ (□.map (pack t) ⨾ □.map t)) =[ _ ^⨾′ □.map⨾ ]=
     ⨾₂ (□.𝟙-codistr ⨾ □.map (pack t ⨾ t))          [■]

    module loopy-conditions = loopy-setup.conditions key key-law f
    open loopy-conditions public using (t ; fixpt)
