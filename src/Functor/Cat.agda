-- Functor categories
open import Shim
module Functor.Cat l m n where

private module records where
  open import Cat l m n
  open import Functor l m n

  -- A natural transformation
  record _~>_ {A B : Cat} (f g : Functor A B) : Type (l ⊔ m ⊔ n) where
    private module A = Cat A
    private module B = Cat B
    private module f = Functor f
    private module g = Functor g
    field run : ∀ a -> (f.run a B.~> g.run a)
    field map : ∀ {a1 a2} -> (p : a1 A.~> a2) -> (run a1 B.⨾ g.map p) B.≈ (f.map p B.⨾ run a2)
  infixl 9 _~>_

  record _≈_ {A B : Cat} {f g : Functor A B} (j k : f ~> g) : Type (l ⊔ n) where
    private module B = Cat B
    private module j = _~>_ j
    private module k = _~>_ k
    field component : ∀ a -> (j.run a B.≈ k.run a)
  infixl 9 _≈_

open import Cat
open import Functor l m n

Hom : Cat l m n -> Cat l m n -> Cat (l ⊔ m ⊔ n) (l ⊔ m ⊔ n) (l ⊔ n)
Hom A B = record
  { Obj = Functor A B
  ; _~>_ = records._~>_
  ; _≈_ = records._≈_
  ; ι₂ = record
    { component = λ _ -> B.ι₂
    }
  ; ÷₂_ = λ
    { u -> let
      private module u = records._≈_ u
      in record
        { component = λ { a -> B.÷₂ (u.component a) }
        }
    }
  ; _⨾₂_ = λ
    { u v -> let
      private module u = records._≈_ u
      private module v = records._≈_ v
      in record
        { component = λ { a -> u.component a B.⨾₂ v.component a }
        }
    }
  ; ι = record
    { run = λ _ -> B.ι
    ; map = λ _ -> B.ι⨾ B.⨾₂ (B.÷₂ B.⨾ι)
    }
  ; ι′ = record
    { component = λ _ -> B.ι₂
    }
  ; _⨾_ = λ
    { j k -> let
      private module j = records._~>_ j
      private module k = records._~>_ k
      in record
        { run = λ a -> j.run a B.⨾ k.run a
        ; map = λ p -> (B.÷₂ B.⨾⨾) B.⨾₂ (_ B.^⨾′ k.map p) B.⨾₂ B.⨾⨾ B.⨾₂ (j.map p B.⨾′^ _) B.⨾₂ (B.÷₂ B.⨾⨾)
        }
    }
  ; _⨾′_ = λ
    { u v -> let
      private module u = records._≈_ u
      private module v = records._≈_ v
      in record
        { component = λ { a -> u.component a B.⨾′ v.component a }
        }
    }
  ; ι⨾ = record
    { component = λ _ -> B.ι⨾
    }
  ; ⨾ι = record
    { component = λ _ -> B.⨾ι
    }
  ; ⨾⨾ = record
    { component = λ _ -> B.⨾⨾
    }
  } where
    private module A = Cat.Cat A
    private module B = Cat.Cat B
module Hom A B where
  open Cat.Cat (Hom A B) public

  module _~>_ {f} {g} = records._~>_ {A} {B} {f} {g}
  module _≈_ {f} {g} = records._≈_ {A} {B} {f} {g}
