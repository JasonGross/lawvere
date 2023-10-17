open import Shim
open import Cat.Cartesian
open import Functor.LaxMonoidalSemicomonad
open CartesianClosedCat using (ccat ; cat)
module lob-via-diagonal-using-universe
  {l m n}
  (C : CartesianClosedCat l m n)
  (F : LaxMonoidalSemicomonad l m n (ccat C))
  where

import lob (ccat C) F as lob
import diagonal-from-lob-with-universe (ccat C) F as diagonal

private module C = CartesianClosedCat C
private module □ = LaxMonoidalSemicomonad F
open import Presheaf.Hom C.cat
open C hiding (Obj)
open □ using () renaming (run to □ ; cojoin to quot)

module setup
  (u : C.Obj) -- universe of small types
  (𝟙u : 𝟙 ~> u) -- 𝟙 is a small type
  (uHom : u × u ~> u) -- u has u-small arrows
  (□-in-u : □ u ~> u) -- "□" is itself an arrow that can act on this small universe
  {p} (is-small : C.Obj -> Type p)
  (s : C.Obj) -- ∃[ s' ∈ C.Obj (small) ] (s' ~> u)
  (if_⨾proj1-dec-eq-□_then_⨾proj2-else_
    : ∀ {a} -> (a ~> s) -> (sv : C.Obj) -> (a ~> □ sv) -> (a ~> u) -> (a ~> u))
  (pair-s : ∀ (v : C.Obj) -> is-small v -> (v ~> u) -> (𝟙 ~> s))
  (□-small : ∀ {a} -> is-small (□ a))
  (exp-small : ∀ {a b} -> is-small a -> is-small b -> is-small (a ^ b))

  (dec-eq-true : ∀ {a a′} {f : a ~> s} {sv : C.Obj} {g : a ~> □ sv} {h : a ~> u} {small-pf : is-small (□ sv)} {j : a′ ~> a} {k : □ sv ~> u}
    -> ((j ⨾ f) ≈ (* ⨾ pair-s (□ sv) small-pf k))
    -> (j ⨾ if f ⨾proj1-dec-eq-□ sv then g ⨾proj2-else h) ≈ (j ⨾ (g ⨾ k)))

  (el : (𝟙 ~> u) -> C.Obj)
  (lift : ∀ (v : C.Obj) -> is-small v -> (𝟙 ~> u))
  (el-fwd : ∀ {a b} -> a ≈ b -> el a ~> el b)
  (lift-exp : ∀ {a b a-sm b-sm} -> (dup ⨾ ((lift a a-sm ×× lift b b-sm) ⨾ uHom)) ≈ lift (b ^ a) (exp-small b-sm a-sm))
  (el-lift-bak : ∀ {a a-sm} -> a ~> el (lift a a-sm))
  (el-lift-fwd : ∀ {a a-sm} -> el (lift a a-sm) ~> a)
  (el-fwd⨾ : ∀ {a b c} {ab : a ≈ b} {bc : b ≈ c} -> (el-fwd ab ⨾ el-fwd bc) ≈ el-fwd (ab ⨾₂ bc))
  (el-fwd÷₂ι : ∀ {a b} {ab : a ≈ b} -> el-fwd (÷₂ ab ⨾₂ ab) ≈ ι)
  (el-lift-bak-fwd : ∀ {a a-sm} -> (el-lift-bak {a} {a-sm} ⨾ el-lift-fwd {a} {a-sm}) ≈ ι)
  (□-map-□-in-u : ∀ {f : 𝟙 ~> u} -> ((□.𝟙-codistr ⨾ □.map f) ⨾ □-in-u) ≈ lift (□ (el f)) □-small)
  (lift-exp : ∀ {a b a-sm b-sm} -> (dup ⨾ ((lift a a-sm ×× lift b b-sm) ⨾ uHom)) ≈ lift (b ^ a) (exp-small b-sm a-sm))

  (x : C.Obj)
  -- FIXME: is there a way to avoid needing x to be small?
  (x-small : is-small x)
  where

  el-bak : ∀ {a b} -> a ≈ b -> el b ~> el a
  el-bak f = el-fwd (÷₂ f)

  module diagonal-setup = diagonal.setup u 𝟙u is-small s if_⨾proj1-dec-eq-□_then_⨾proj2-else_ pair-s □-small

  T : □ u ~> u
  T = dup ⨾ ((□-in-u ×× (* ⨾ lift x x-small)) ⨾ uHom) -- λ s. s ~> x

  module diagonal-conditions = diagonal-setup.conditions dec-eq-true T
  open diagonal-conditions using () renaming (fixpt to ΔT')

  ΔT : C.Obj
  ΔT = el (fst ΔT')

  pack-helper : fst ΔT' ≈ lift (x ^ □ ΔT) (exp-small x-small □-small)
  pack-helper
    =  (fst ΔT')                                                                                                                  =[ snd ΔT' ]=
    ⨾₂ ((□.𝟙-codistr ⨾ □.map (fst ΔT')) ⨾ (dup ⨾ ((□-in-u ×× (* ⨾ lift x x-small)) ⨾ uHom)))                                      =[ ⨾⨾ ⨾₂ ((dup⨾ ⨾′^ _) ⨾₂ ÷₂ ⨾⨾) ]=
    ⨾₂ (dup ⨾ (((□.𝟙-codistr ⨾ □.map (fst ΔT')) ×× (□.𝟙-codistr ⨾ □.map (fst ΔT'))) ⨾ ((□-in-u ×× (* ⨾ lift x x-small)) ⨾ uHom))) =[ _ ^⨾′ (⨾⨾ ⨾₂ (××⨾ ⨾₂ (ι₂ ××′ (⨾⨾ ⨾₂ (*′ ⨾′^ _))) ⨾′^ _)) ]=
    ⨾₂ (dup ⨾ ((((□.𝟙-codistr ⨾ □.map (fst ΔT')) ⨾ □-in-u) ×× (* ⨾ lift x x-small)) ⨾ uHom))                                      =[ _ ^⨾′ ((□-map-□-in-u ××′ (*′ ⨾′^ _ ⨾₂ ι⨾)) ⨾′^ _) ]=
    ⨾₂ (dup ⨾ ((lift (□ ΔT) □-small ×× lift x x-small) ⨾ uHom))                                                                   =[ lift-exp ]=
    ⨾₂ lift (x ^ □ ΔT) (exp-small x-small □-small)                                                                                 [■]
    where open diagonal-setup.notations

  pack : (□ ΔT ~> x) -> 𝟙 ~> □ ΔT
  pack t = □.𝟙-codistr ⨾ □.map (lambda t ⨾ (el-lift-bak ⨾ el-bak pack-helper))

  private module lob-setup = lob.setup x ΔT pack
  open lob-setup public using (Fixpoint ; introspect ; module notations)
  open notations

  unpack : (ΔT × □ ΔT) ~> x
  unpack = ((el-fwd pack-helper ⨾ el-lift-fwd) ×× ι) ⨾ apply

  unpack-point-surjection : ∀ {f : □ ΔT ~> x} {g : 𝟙 ~> □ (□ ΔT)}
      -> (dup ⨾ ((pack f ×× g) ⨾ (□.×-codistr ⨾ □.map unpack))) ≈ (g ⨾ □.map f)
  unpack-point-surjection {f} {g}
    =  (dup ⨾ ((pack f ×× g) ⨾ (□.×-codistr ⨾ □.map unpack)))                                                      =[ _ ^⨾′ ((ι₂ ××′ (÷₂ ((_ ^⨾′ □.mapι) ⨾₂ ⨾ι))) ⨾′^ _) ]=
    ⨾₂ (dup ⨾ ((pack f ×× (g ⨾ □.map ι)) ⨾ (□.×-codistr ⨾ □.map unpack)))                                          =[ _ ^⨾′ (÷₂ (⨾⨾ ⨾₂ (××⨾ ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ ((□.map (lambda f ⨾ (el-lift-bak ⨾ el-bak pack-helper)) ×× □.map ι) ⨾ (□.×-codistr ⨾ □.map unpack)))) =[ _ ^⨾′ (_ ^⨾′ ⨾⨾) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (((□.map (lambda f ⨾ (el-lift-bak ⨾ el-bak pack-helper)) ×× □.map ι) ⨾ □.×-codistr) ⨾ □.map unpack))) =[ _ ^⨾′ (_ ^⨾′ (□.××-codistr ⨾′^ _)) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ ((□.×-codistr ⨾ (□.map (((lambda f ⨾ (el-lift-bak ⨾ el-bak pack-helper))) ×× ι))) ⨾ □.map unpack)))   =[ _ ^⨾′ (_ ^⨾′ ((÷₂ ⨾⨾) ⨾₂ (_ ^⨾′ □.map⨾))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (((lambda f ⨾ (el-lift-bak ⨾ el-bak pack-helper)) ×× ι) ⨾ unpack))))             =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (⨾⨾ ⨾₂ (××⨾ ⨾′^ _)))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map ((((lambda f ⨾ (el-lift-bak ⨾ el-bak pack-helper)) ⨾ (el-fwd pack-helper ⨾ el-lift-fwd)) ×× (ι ⨾ ι)) ⨾ apply)))) =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (((÷₂ ⨾⨾ ⨾₂ (_ ^⨾′ (÷₂ ⨾⨾ ⨾₂ (_ ^⨾′ ⨾⨾)))) ××′ ι⨾) ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (((lambda f ⨾ (el-lift-bak ⨾ ((el-bak pack-helper ⨾ el-fwd pack-helper) ⨾ el-lift-fwd))) ×× ι) ⨾ apply))))       =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (((_ ^⨾′ (_ ^⨾′ ((el-fwd⨾ ⨾₂ el-fwd÷₂ι) ⨾′^ _))) ××′ ι₂) ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (((lambda f ⨾ (el-lift-bak ⨾ (ι ⨾ el-lift-fwd))) ×× ι) ⨾ apply))))               =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (((_ ^⨾′ _ ^⨾′ ι⨾) ××′ ι₂) ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (((lambda f ⨾ (el-lift-bak ⨾ el-lift-fwd)) ×× ι) ⨾ apply))))                     =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (((_ ^⨾′ el-lift-bak-fwd) ××′ ι₂) ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (((lambda f ⨾ ι) ×× ι) ⨾ apply))))                        =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ ((⨾ι ××′ ι₂) ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map ((lambda f ×× ι) ⨾ apply))))                              =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ lambda-apply)) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map ((getr ⨾ ι) ⨾ f))))                                       =[ _ ^⨾′ (_ ^⨾′ (_ ^⨾′ □.map′ (⨾ι ⨾′^ _))) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (□.×-codistr ⨾ □.map (getr ⨾ f))))                                             =[ _ ^⨾′ (_ ^⨾′ ((_ ^⨾′ ÷₂ □.map⨾) ⨾₂ ⨾⨾)) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ ((□.×-codistr ⨾ □.map getr) ⨾ □.map f)))                                       =[ _ ^⨾′ (_ ^⨾′ (□.×-codistr-getr ⨾′^ _)) ]=
    ⨾₂ (dup ⨾ ((□.𝟙-codistr ×× g) ⨾ (getr ⨾ □.map f)))                                                             =[ _ ^⨾′ ⨾⨾ ]=
    ⨾₂ (dup ⨾ (((□.𝟙-codistr ×× g) ⨾ getr) ⨾ □.map f))                                                             =[ _ ^⨾′ ((getr⨾ ⨾′^ _)) ]=
    ⨾₂ (dup ⨾ ((getr ⨾ g) ⨾ □.map f))                                                                              =[ (_ ^⨾′ ÷₂ ⨾⨾) ⨾₂ ⨾⨾ ]=
    ⨾₂ ((dup ⨾ getr) ⨾ (g ⨾ □.map f))                                                                              =[ dup-getr ⨾′^ _ ]=
    ⨾₂ (ι ⨾ (g ⨾ □.map f))                                                                                         =[ ι⨾ ]=
    ⨾₂ (g ⨾ □.map f)                                                                                                [■]

  module conditions
    (f : □ x ~> x)
    where

    private module lob-conditions = lob-setup.conditions unpack unpack-point-surjection f
    open lob-conditions public using (key ; key-law ; t ; fixpt)
