open import Shim
import Cat
-- TODO: naming?
module Presheaf.Hom {l m n} (C : Cat.Cat l m n) where
open import Presheaf l m n m n
private module C = Cat.Cat C
open C

-- TODO: Naming?
-- TODO: Should these records be written down somewhere non-anonymously?
∙~>_ : C.Obj -> Presheaf C
∙~>_ a2 = record
  { Run = λ{ a1 -> record { Obj = a1 ~> a2 ; _~_ = _≈_ ; ι = ι₂ ; ÷_ = ÷₂_ ; _⨾_ = _⨾₂_ } }
  ; Map = λ f → record { run = f ⨾_ ; map = f ^⨾′_ }
  ; Map′ = λ e → record { component = e ⨾′^_ }
  ; Map-ι = record { component = λ{ _ -> ÷₂ ι⨾ } }
  ; Map-⨾ = λ{ f g -> record { component = λ{ a -> ⨾⨾ } } }
  }
infix 9 ∙~>_


-- TODO: implicit status?
-- TODO: naming
module ∙~>_ a = Presheaf (∙~> a)
