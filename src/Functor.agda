open import Shim
-- TODO: Naming
module Functor l m n where
open import Cat l m n

record Functor (A B : Cat) : Type (l ⊔ m ⊔ n) where
  private module A = Cat A
  private module B = Cat B
  field run : A.Obj -> B.Obj
  field map : ∀ {a1 a2} -> a1 A.~> a2 -> run a1 B.~> run a2

  field mapι : ∀ {a} -> map (A.ι {a}) B.≈ B.ι {run a}
  field map⨾ : ∀ {a1 a2 a3} {f1 : a1 A.~> a2} {f2 : a2 A.~> a3} -> (map f1 B.⨾ map f2) B.≈ map (f1 A.⨾ f2)

  field map′ : ∀ {a1 a2} {f1 f2 : a1 A.~> a2} -> (f1 A.≈ f2) -> (map f1) B.≈ (map f2)
