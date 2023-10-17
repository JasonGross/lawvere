open import Shim
module Functor.LaxMonoidalSemicomonad l m n where
open import Cat l m n
open import Cat.Cartesian l m n
open import Functor l m n
open import Functor.LaxMonoidal l m n
open import Functor.Semicomonad l m n
open CartesianCat using (cat)

record IsLaxMonoidalSemicomonadCompat
       {C : CartesianCat} {F : Functor (C .cat) (C .cat)}
       (LM : IsLaxMonoidal C C F)
       (S : IsSemicomonad F)
       : Type (l ⊔ m ⊔ n) where
  private module C = CartesianCat C
  private module F = Functor F
  private module LM = IsLaxMonoidal LM
  private module S = IsSemicomonad S
  open C
  open F
  open LM
  open S

  -- points are quoted with `F.𝟙-codistr ⨾ F.map`, quoted terms are
  -- requoted with `cojoin`; these must agree on closed quoted terms
  field map-cojoin : ∀ {a} {f : 𝟙 ~> run a} -> (f ⨾ cojoin) ≈ (𝟙-codistr ⨾ map f)
  -- TODO: Where does this fit in?  Is it part of LaxMonoidal?
  field ×-codistr-dup  : ∀ {a} -> (dup {run a} ⨾ ×-codistr) ≈ map dup
  field ×-codistr-getl : ∀ {a b} -> (×-codistr {a} {b} ⨾ map getl) ≈ getl
  field ×-codistr-getr : ∀ {a b} -> (×-codistr {a} {b} ⨾ map getr) ≈ getr

record IsLaxMonoidalSemicomonad (C : CartesianCat) (F : Functor (C .cat) (C .cat)) : Type (l ⊔ m ⊔ n) where
  field lm : IsLaxMonoidal C C F
  field s : IsSemicomonad F
  field compat : IsLaxMonoidalSemicomonadCompat lm s
  private module lm = IsLaxMonoidal lm
  private module s = IsSemicomonad s
  private module compat = IsLaxMonoidalSemicomonadCompat compat
  open lm public
  open s public
  open compat public

record LaxMonoidalSemicomonad (C : CartesianCat) : Type (l ⊔ m ⊔ n) where
  field functor : Functor (C .cat) (C .cat)
  field lms : IsLaxMonoidalSemicomonad C functor
  private module functor = Functor functor
  private module lms = IsLaxMonoidalSemicomonad lms
  open functor public
  open lms public
