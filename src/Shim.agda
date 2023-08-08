module Shim where
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) renaming (Set to Type; Setω to Typeω) public

data _⊑_ (l : Level) : Level -> Type where
  lprec : ∀ b -> l ⊑ (l ⊔ b)

_=>_ : ∀ {l} -> Type l -> Type l -> Type l
A => B = A -> B
infix 1 _=>_

_⇒_ : ∀ {l} -> Type l -> Type l -> Type l
A ⇒ B = A => B
infix 1 _⇒_

record ⊤ {l} : Type l where
  constructor ⋆
open ⊤ public

data ⊥ {l} : Type l where

! : ∀ {l} {m} {R : Type m} -> ⊥ {l} -> R
! ()

record _∧_ {l} (A B : Type l) : Type l where
  constructor _,_
  field outl : A
  field outr : B
open _∧_ using (outl; outr) public
infixl 6 _∧_
infixl 1 _,_

data _∨_ {l} (A B : Type l) : Type l where
  inl : A -> (A ∨ B)
  inr : B -> (A ∨ B)
infixl 4 _∨_

record exists {l} {A : Type l} {m} (B : A → Type m) : Type (l ⊔ m) where
  constructor _▷_
  field fst : A
  field snd : B fst
open exists using (fst; snd) public
infixl 0 _▷_

syntax exists {A = A} (λ a -> B) = ∃[ a ∈ A ] B
infix 5 exists
