open import Shim
open import Cat.Cartesian
open import Functor.LaxMonoidalSemicomonad
module diagonal-from-lob-with-universe
  {l m n}
  (C : CartesianCat l m n)
  (F : LaxMonoidalSemicomonad l m n C)
  where

import lob C F as lob

private module C = CartesianCat C
private module □ = LaxMonoidalSemicomonad F
open import Presheaf.Hom C.cat
open C hiding (Obj)
open □ using () renaming (run to □ ; cojoin to quot)

module setup
  (u : C.Obj) -- universe of small types
  (𝟙u : 𝟙 ~> u) -- 𝟙 is a small type
  {p} (is-small : C.Obj -> Type p)
  (s : C.Obj) -- ∃[ s' ∈ C.Obj (small) ] (s' ~> u)
  (if_⨾proj1-dec-eq-□_then_⨾proj2-else_
    : ∀ {a} -> (a ~> s) -> (sv : C.Obj) -> (a ~> □ sv) -> (a ~> u) -> (a ~> u))
  (pair-s : ∀ (v : C.Obj) -> is-small v -> (v ~> u) -> (𝟙 ~> s))
  (□-small : ∀ {a} -> is-small (□ a))
  where

  pack : (□ s ~> u) -> 𝟙 ~> □ s
  pack t = □.𝟙-codistr ⨾ □.map (pair-s (□ s) □-small t)

  private module loopy-setup = lob.setup u s pack
  open loopy-setup public using (Fixpoint ; introspect ; module notations)
  open notations

  unpack : (s × □ s) ~> u
  unpack = if getl ⨾proj1-dec-eq-□ s then
              getr ⨾proj2-else
              (* ⨾ 𝟙u)

  module conditions
    (dec-eq-true : ∀ {a a′} {f : a ~> s} {sv : C.Obj} {g : a ~> □ sv} {h : a ~> u} {small-pf : is-small (□ sv)} {j : a′ ~> a} {k : □ sv ~> u}
      -> ((j ⨾ f) ≈ (* ⨾ pair-s (□ sv) small-pf k))
      -> (j ⨾ if f ⨾proj1-dec-eq-□ sv then g ⨾proj2-else h) ≈ (j ⨾ (g ⨾ k)))
    (f : □ u ~> u)
    where

    unpack-point-surjection : ∀ {f : □ s ~> u} {g : 𝟙 ~> □ (□ s)}
        -> (dup ⨾ ((pack f ×× g) ⨾ (□.×-codistr ⨾ □.map unpack))) ≈ (g ⨾ □.map f)
    unpack-point-surjection {f} {g}
      =  (dup ⨾ ((pack f ×× g) ⨾ (□.×-codistr ⨾ □.map unpack)))                                                      =[ _ ^⨾′ ((ι₂ ××′ (÷₂ ((_ ^⨾′ □.mapι) ⨾₂ ⨾ι))) ⨾′^ _) ]=
      ⨾₂ (dup ⨾ ((pack f ×× (g ⨾ □.map ι)) ⨾ (□.×-codistr ⨾ □.map unpack)))                                          =[ _ ^⨾′ (÷₂ (⨾⨾ ⨾₂ (××⨾ ⨾′^ _))) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ ((□.map (pair-s (□ s) □-small f) ×× □.map ι) ⨾ (□.×-codistr ⨾ □.map unpack)))) =[ _ ^⨾′ (_ ^⨾′ ⨾⨾) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (((□.map (pair-s (□ s) □-small f) ×× □.map ι) ⨾ □.×-codistr) ⨾ □.map unpack))) =[ _ ^⨾′ (_ ^⨾′ (□.××-codistr ⨾′^ _)) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ ((□.×-codistr ⨾ □.map (pair-s (□ s) □-small f ×× ι)) ⨾ □.map unpack)))         =[ _ ^⨾′ (_ ^⨾′ ((÷₂ ⨾⨾) ⨾₂ (_ ^⨾′ □.map⨾))) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map ((pair-s (□ s) □-small f ×× ι) ⨾ unpack))))               =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (dec-eq-true (getl⨾ ⨾₂ (*′ ⨾′^ _))))) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map ((pair-s (□ s) □-small f ×× ι) ⨾ (getr ⨾ f)))))           =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (⨾⨾ ⨾₂ (getr⨾ ⨾′^ _)))) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map ((getr ⨾ ι) ⨾ f))))                                       =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (⨾ι ⨾′^ _))) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (getr ⨾ f))))                                             =[ _ ^⨾′ (_ ^⨾′ ((_ ^⨾′ ÷₂ □.map⨾) ⨾₂ ⨾⨾)) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ ((□.×-codistr ⨾ □.map getr) ⨾ □.map f)))                                       =[ _ ^⨾′ (_ ^⨾′ (□.×-codistr-getr ⨾′^ _)) ]=
      ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (getr ⨾ □.map f)))                                                             =[ _ ^⨾′ ⨾⨾ ]=
      ⨾₂ (dup ⨾ (((□.𝟙-codistr ×× g) ⨾ getr) ⨾ □.map f))                                                             =[ _ ^⨾′ ((getr⨾ ⨾′^ _)) ]=
      ⨾₂ (dup ⨾ ((getr ⨾ g) ⨾ □.map f))                                                                              =[ (_ ^⨾′ ÷₂ ⨾⨾) ⨾₂ ⨾⨾ ]=
      ⨾₂ ((dup ⨾ getr) ⨾ (g ⨾ □.map f))                                                                              =[ dup-getr ⨾′^ _ ]=
      ⨾₂ (ι ⨾ (g ⨾ □.map f))                                                                                         =[ ι⨾ ]=
      ⨾₂ (g ⨾ □.map f)                                                                                                [■]

    private module loopy-conditions = loopy-setup.conditions unpack unpack-point-surjection f
    open loopy-conditions public using (key ; key-law ; t ; fixpt)
