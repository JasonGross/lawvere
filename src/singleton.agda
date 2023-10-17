open import Shim
open import Cat.Cartesian
open import Presheaf as _
open CartesianCat using (cat)
module singleton
  {l m n sl sm}
  (C : CartesianCat l m n)
  (A : Presheaf l m n sl sm (C .cat))
  where

import loopy C A as loopy

private module C = CartesianCat C
private module A = Presheaf A
open C hiding (Obj)
open A using (_»_)

module setup
  (a : C.Obj)
  (reflect : A.Run.Obj 𝟙 -> 𝟙 ~> a)

  (s : C.Obj)

  (pack : A.Run.Obj s -> 𝟙 ~> s)
  where

  private module loopy-setup = loopy.setup (λ{ _ -> ⊤ {lzero} }) a (λ{ (x ▷ _) -> reflect x })
  open loopy-setup public using (module notations)

  Fixpoint : A.Run.Obj a -> Type (sl ⊔ sm)
  Fixpoint f = ∃[ x ∈ A.Run.Obj 𝟙 ] (x A.≈ (reflect x » f))

  private module loopy-conditions₁ = loopy-setup.conditions₁ s (λ{ _ -> ⊤ {lzero} }) (λ{ (x ▷ _) -> pack x }) (λ{ _ -> ⋆ })

  introspect : A.Run.Obj s -> A.Run.Obj 𝟙
  introspect t = fst (loopy-conditions₁.introspect (t ▷ ⋆))

  module conditions
    (key : s ~> a)
    (key-law : ∀ {t : A.Run.Obj s} -> (pack t ⨾ key) ≈ reflect (introspect t))

    (f : A.Run.Obj a)
    where

    private module loopy-conditions₂ = loopy-conditions₁.conditions₂ key key-law f
    open loopy-conditions₂ public using (t)

    private module loopy-theorem = loopy-conditions₂.theorem ⋆

    fixpt : Fixpoint f
    fixpt = fst (fst loopy-theorem.fixpt) ▷ loopy-theorem.fixpt.proof
