open import Shim
module Functor.Semicomonad l m n where
open import Cat l m n
open import Functor l m n

record IsSemicomonad {C : Cat} (F : Functor C C) : Type (l ⊔ m ⊔ n) where
  private module C = Cat C
  private module F = Functor F
  open C
  open F
  field cojoin : ∀ {a : C.Obj} -> run a ~> run (run a)
  field cojoin-cohere : ∀ {a : C.Obj} -> (cojoin {a} ⨾ cojoin {run a}) ≈ (cojoin {a} ⨾ map (cojoin {a}))

record Semicomonad (C : Cat) : Type (l ⊔ m ⊔ n) where
  field functor : Functor C C
  field issemicomonad : IsSemicomonad functor
  private module functor = Functor functor
  private module issemicomonad = IsSemicomonad issemicomonad
  open functor public
  open issemicomonad public
