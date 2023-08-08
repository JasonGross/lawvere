open import Shim
module Set.Cat l m where
open import Cat (lsuc (l ⊔ m)) (l ⊔ m) (l ⊔ m)

private module records where
  open import Set l m public

  record _~>_ (A B : Set) : Type (l ⊔ m) where
    private module A = Set A
    private module B = Set B
    field run : A.Obj => B.Obj
    field map : ∀ {a1 a2} -> (a1 A.~ a2) -> (run a1 B.~ run a2)
  infixl 9 _~>_

  record _≈_ {A B : Set} (f g : A ~> B) : Type (l ⊔ m) where
    private module A = Set A
    private module B = Set B
    private module f = _~>_ f
    private module g = _~>_ g
    field component : ∀ a -> (f.run a B.~ g.run a)
  infixl 9 _≈_

Set : Cat
Set = record
  { Obj = records.Set
  ; _~>_ = records._~>_
  ; _≈_ = records._≈_
  ; ι₂ = λ
    { {A} {B} -> let
      private module A = records.Set A
      private module B = records.Set B
      in record
      { component = λ{ a -> B.ι }
      }
    }
  ; ÷₂_ = λ
    { {A} {B} p -> let
      private module A = records.Set A
      private module B = records.Set B
      private module p = records._≈_ p
      in record
      { component = λ{ a -> B.÷ p.component a }
      }
    }
  ; _⨾₂_ = λ
    { {A} {B} p q -> let
      private module A = records.Set A
      private module B = records.Set B
      private module p = records._≈_ p
      private module q = records._≈_ q
      in record
      { component = λ{ a -> p.component a B.⨾ q.component a }
      }
    }
  ; ι = record
    { run = λ{ a -> a }
    ; map = λ{ p -> p }
    }
  ; ι′ = λ
    { {A} -> let
      private module A = records.Set A
      in record
      { component = λ{ a -> A.ι }
      }
    }
  ; _⨾_ = λ
    { f g -> let
      private module f = records._~>_ f
      private module g = records._~>_ g
      in record
      { run = λ{ a -> g.run (f.run a) }
      ; map = λ{ p -> g.map (f.map p) }
      }
    }
  ; _⨾′_ = λ
    { {A} {B} {C} {f1} {f2} p {g1} {g2} q -> let
      private module A = records.Set A
      private module B = records.Set B
      private module C = records.Set C
      private module f1 = records._~>_ f1
      private module f2 = records._~>_ f2
      private module g1 = records._~>_ g1
      private module g2 = records._~>_ g2
      private module p = records._≈_ p
      private module q = records._≈_ q
      in record
      { component = λ{ a -> g1.map (p.component a) C.⨾ q.component (f2.run a) }
      }
    }
  ; ι⨾ = λ
    { {A} {B} {f} -> let
      private module A = records.Set A
      private module B = records.Set B
      in record
      { component = λ{ a -> B.ι }
      }
    }
  ; ⨾ι = λ
    { {A} {B} {f} -> let
      private module A = records.Set A
      private module B = records.Set B
      in record
      { component = λ{ a -> B.ι }
      }
    }
  ; ⨾⨾ = λ
    { {A} {B} {C} {D} {f} {g} {h} -> let
      private module A = records.Set A
      private module B = records.Set B
      private module C = records.Set C
      private module D = records.Set D
      in record
      { component = λ{ a -> D.ι }
      }
    }
  }
module Set where
  open Cat Set public
  open records public using (module _~>_ ; module _≈_) renaming (module Set to Obj)
