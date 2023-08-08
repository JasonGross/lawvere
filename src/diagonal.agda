open import Shim
open import Cat.Cartesian
open import Presheaf as _
open CartesianCat using (cat)
module diagonal
  {l m n sl sm}
  (CtxCat : CartesianCat l m n)
  (TyCat : Presheaf l m n sl sm (CtxCat .cat))
  where

private module CtxCat = CartesianCat CtxCat
private module TyCat = Presheaf TyCat
open CtxCat renaming (Obj to Ctx)
open TyCat using (_»_)
open TyCat.Run using () renaming (Obj to Ty)

import singleton CtxCat TyCat as loopy

module setup
  (QCtx : Ctx)
  (quot : Ty 𝟙 -> 𝟙 ~> QCtx)

  (s : Ctx) -- Σ* QCtx QTy
  (pack : Ty s -> 𝟙 ~> s) -- quotation of the type & context

  where

  private module loopy-setup = loopy.setup QCtx quot s pack
  open loopy-setup public using (Fixpoint ; introspect ; module notations)

  module conditions
    (key : s ~> QCtx) -- TODO: What should this be?
    (key-law : ∀ {t : Ty s} -> (pack t ⨾ key) ≈ quot (introspect t)) -- TODO: What should this be?

    (f : Ty QCtx)
    where

    private module loopy-conditions = loopy-setup.conditions key key-law f
    open loopy-conditions public using (t ; fixpt)
