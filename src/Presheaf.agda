open import Shim
module Presheaf l m where
open import Cat (lsuc (l ⊔ m)) (l ⊔ m) (l ⊔ m)
open import Set.Cat l m

record Presheaf (A : Cat) : Type (lsuc (l ⊔ m)) where
    private module A = Cat A
    field Run : A.Obj => Set.Obj
    field Map : ∀ {a1 a2 : A.Obj} -> (a2 A.~> a1) -> (Run a1 Set.~> Run a2)
    field Map′ : ∀ {a1 a2 : A.Obj} {f1 f2 : a2 A.~> a1} -> (f1 A.≈ f2) -> Map f1 Set.≈ Map f2
    field Map-ι : ∀ {a : A.Obj} -> Set.ι {Run a} Set.≈ Map (A.ι {a})
    field Map-⨾ : ∀ {a1 a2 a3 : A.Obj} (f : a1 A.~> a2) (g : a2 A.~> a3) -> (Map g Set.⨾ Map f) Set.≈ Map (f A.⨾ g)
