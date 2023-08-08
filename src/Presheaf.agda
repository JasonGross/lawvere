open import Shim
module Presheaf l m n sl sm where
open import Cat l m n
open import Set.Cat sl sm

record Presheaf (A : Cat) : Type (lsuc (sl ⊔ sm) ⊔ l ⊔ m ⊔ n) where
  private module A = Cat A
  field Run : A.Obj -> Set.Obj
  module Run a = Set.Obj (Run a)
  private module Run-implicit {a} = Run a
  field Map : ∀ {a1 a2 : A.Obj} -> (a2 A.~> a1) -> (Run a1 Set.~> Run a2)
  module Map {a1} {a2} f = Set._~>_ (Map {a1} {a2} f)
  field Map′ : ∀ {a1 a2 : A.Obj} {f1 f2 : a2 A.~> a1} -> (f1 A.≈ f2) -> Map f1 Set.≈ Map f2
  module Map′ {a1} {a2} {f1} {f2} f12 = Set._≈_ (Map′ {a1} {a2} {f1} {f2} f12)
  field Map-ι : ∀ {a : A.Obj} -> Map (A.ι {a}) Set.≈ Set.ι {Run a}
  module Map-ι {a} = Set._≈_ (Map-ι {a})
  field Map-⨾ : ∀ {a1 a2 a3 : A.Obj} (f : a1 A.~> a2) (g : a2 A.~> a3) -> (Map g Set.⨾ Map f) Set.≈ Map (f A.⨾ g)
  module Map-⨾ {a1} {a2} {a3} f g = Set._≈_ (Map-⨾ {a1} {a2} {a3} f g)

  open Run-implicit public using ()
    renaming (_~_ to _≈_ ; ι to ι₂ ; ÷_ to ÷₂_ ; _⨾_ to _⨾′_)
  open Map public using ()
    renaming (run to infixr 9 _»_)
