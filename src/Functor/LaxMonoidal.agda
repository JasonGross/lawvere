open import Shim
module Functor.LaxMonoidal l m n where
open import Cat l m n
open import Cat.Cartesian l m n
open import Functor l m n
open CartesianCat using (cat)

record IsLaxMonoidal (A B : CartesianCat) (F : Functor (A .cat) (B .cat)) : Type (l ⊔ m ⊔ n) where
  private module A = CartesianCat A
  private module B = CartesianCat B
  private module F = Functor F
  open F
  field 𝟙-codistr : B.𝟙 B.~> run A.𝟙
  field ×-codistr  : ∀ {a1 a2} -> (run a1 B.× run a2) B.~> run (a1 A.× a2)

  -- naturality for run-×-codistr
  field ××-codistr : ∀ {a1 a2 a1′ a2′} {f : a1 A.~> a2} {f′ : a1′ A.~> a2′}
                     -> ((map f B.×× map f′) B.⨾ ×-codistr) B.≈ (×-codistr B.⨾ map (f A.×× f′))

  -- TODO: interaction with (not yet written ×-assoc)
  -- TODO: unitality interaction

record LaxMonoidal (A B : CartesianCat) : Type (l ⊔ m ⊔ n) where
  field functor : Functor (A .cat) (B .cat)
  field islaxmonoidal : IsLaxMonoidal A B functor
  private module functor = Functor functor
  private module islaxmonoidal = IsLaxMonoidal islaxmonoidal
  open functor public
  open islaxmonoidal public
