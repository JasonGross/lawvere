open import Shim
module IndexedSet l m where
open import Set.Cat l m

-- A presheaf on `lift A`.
-- This representation is more convenient than defining `lift : Set -> Cat`.
record IndexedSet (A : Set.Obj) : Type (lsuc (l ⊔ m)) where
  private module A = Set.Obj A

  field Run : A.Obj -> Set.Obj
  module Run a = Set.Obj (Run a)
  private module Run-implicit {a} = Run a

  field Map : ∀ {a1 a2} -> (a2 A.~ a1) -> (Run a1 Set.~> Run a2)
  module Map {a1} {a2} f = Set._~>_ (Map {a1} {a2} f)

  field Map′ : ∀ {a1 a2} {f1 f2 : a2 A.~ a1} -> Map f1 Set.≈ Map f2
  module Map′ {a1} {a2} {f1} {f2} = Set._≈_ (Map′ {a1} {a2} {f1} {f2})

  field Map-ι : ∀ {a} -> Set.ι {Run a} Set.≈ Map (A.ι {a})
  module Map-ι {a} = Set._≈_ (Map-ι {a})

  field Map-⨾ : ∀ {a1 a2 a3} (f : a1 A.~ a2) (g : a2 A.~ a3) -> (Map g Set.⨾ Map f) Set.≈ Map (f A.⨾ g)
  module Map-⨾ {a1} {a2} {a3} f g = Set._≈_ (Map-⨾ {a1} {a2} {a3} f g)

  -- Copied from Presheaf
  open Run-implicit public using ()
    renaming (_~_ to _≈_ ; ι to ι₂ ; ÷_ to ÷₂_ ; _⨾_ to _⨾′_)
  open Map public using ()
    renaming (run to infixr 9 _»_)
