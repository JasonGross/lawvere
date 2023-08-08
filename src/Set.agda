open import Shim
module Set l m where

record Set : Type (lsuc (l ⊔ m)) where

    field Obj : Type l

    field _~_ : Obj -> Obj -> Type m
    infix 1 _~_ 

    field ι : ∀ {a} -> (a ~ a)

    field ÷_ : ∀ {a1 a2} -> (a1 ~ a2) -> (a2 ~ a1)

    field _⨾_ : ∀ {a1 a2 a3} -> (a1 ~ a2) -> (a2 ~ a3) -> (a1 ~ a3)
    infixl 9 _⨾_
