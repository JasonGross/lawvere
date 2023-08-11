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
open CtxCat using () renaming
  (Obj to Ctx ; _~>_ to CtxSubst ; 𝟙 to ε ; * to σε
  ; ι to ισ ; _⨾_ to _σ⨾_ ; _≈_ to _σ≈_ ; _⨾₂_ to _σ⨾₂_ ; ι₂ to σι₂)
open TyCat.Run using () renaming (Obj to Ty)
open TyCat.Map using () renaming (run to subst)
_[_] : ∀ {Γ Γ′} -> Ty Γ′ -> CtxSubst Γ Γ′ -> Ty Γ
T [ σ ] = subst σ T

import singleton CtxCat TyCat as loopy

module setup
  {tm} (Tm : ∀ {Γ} -> Ty Γ -> Type tm)
  (_[→]_ : ∀ {Γ} (A B : Ty Γ) -> Ty Γ)
  ([𝟙] : ∀ {Γ} -> Ty Γ)
  (_,_ : ∀ (Γ : Ctx) (T : Ty Γ) -> Ctx)
  (_[▷]_ : ∀ {Z A X} -> (a : CtxSubst Z A) -> Tm {Z} ([𝟙] [→] (X [ a ])) -> CtxSubst Z (A , X))
  (fst : ∀ {A X} -> CtxSubst (A , X) A)
  (var₀ : ∀ {Γ X} -> Tm {Γ , X} ([𝟙] [→] (X [ fst ])))

  ([Ctx] : ∀ {Γ} -> Ty Γ)
  ([Ty] : ∀ {Γ1 Γ2} {σ : CtxSubst Γ1 Γ2} -> Tm {Γ1} ([𝟙] [→] ([Ctx] [ σ ])) -> Ty Γ1)

  ([Ty]-var₀-unsubst-[▷] : ∀ {Γ} {σ : CtxSubst Γ Γ} {qΓ : Tm ([𝟙] [→] ([Ctx] [ σ ]))}
    -> Tm {Γ} ([𝟙] [→] ([Ty] qΓ [ σ ]))
    -> Tm {Γ} ([𝟙] [→] ([Ty] var₀ [ σ [▷] qΓ ])))
  (⌜_⌝c : ∀ {Γ Γ′} {σ : CtxSubst Γ Γ′} -> (Γ′′ : Ctx) -> Tm {Γ} ([𝟙] [→] ([Ctx] [ σ ]))) -- σ is irrelevant
  (⌜_⌝T : ∀ {Γ1 Γ2 Γ3 Γ4} {σ1 : CtxSubst Γ2 Γ3} {σ2 : CtxSubst Γ3 Γ4} -> (T : Ty Γ1) ->
    Tm {Γ2} ([𝟙] [→] (([Ty] {σ = σ2} ⌜ Γ1 ⌝c) [ σ1 ])))
  where

  wk : ∀ {Γ X} -> Ty Γ -> Ty (Γ , X)
  wk T = T [ fst ]

  private
    module loopy-setup = loopy.setup
      (ε , [Ty] {σ = ισ} ⌜ ε ⌝c)
      (λ{ T -> ισ [▷] ⌜ T ⌝T })
      ((ε , [Ctx]) , [Ty] var₀)
      (λ{ T -> (ισ [▷] ⌜ (ε , [Ctx]) , [Ty] var₀ ⌝c) [▷] [Ty]-var₀-unsubst-[▷] ⌜ T ⌝T })
  open loopy-setup public using (Fixpoint ; introspect ; module notations)
  module σnotations where
    chain : ∀ {Γ Γ′} {f g : CtxSubst Γ Γ′} -> f σ≈ g -> f σ≈ g
    chain x = x

    syntax chain {f = f} pf = f =[ pf ]=

    _[■] : ∀ {Γ Γ′} (f : CtxSubst Γ Γ′) -> f σ≈ f
    f [■] = σι₂
  open σnotations

  module conditions
    {tme} (_Tm≈_ : ∀ {Γ T} -> Tm {Γ} T -> Tm {Γ} T -> Type tme)
    (_[⨾]_ : ∀ {Γ1 Γ2 Γ3 A B C} {σ1 : CtxSubst Γ1 Γ2} {σ2 : CtxSubst Γ2 Γ3}
      -> Tm {Γ1} (A [→] (B [ σ1 ])) -> Tm {Γ2} (B [→] (C [ σ2 ])) -> Tm {Γ1} (A [→] (C [ σ1 σ⨾ σ2 ])))
    ([▷]-fst : ∀ {Z A X a b} -> (_[▷]_ {Z} {A} {X} a b σ⨾ fst) σ≈ a)

    -- TODO: more principled version of this; what is this?
    (map-wk2-ctx-subst : ∀ {A B C T} -> (σ : Tm {(ε , A) , B} ([𝟙] [→] (C [ σε ])))
      -> Tm {(ε , A) , B} (wk (wk T) [→] ((wk T) [ σε [▷] σ ])))
    -- TODO: more principled version, where does this come from???
    (map-unsubst : ∀ {Γ1 Γ2 Γ3 A B} {σ1 : CtxSubst Γ1 Γ2} {σ2 : CtxSubst Γ2 Γ3} {σ3 : CtxSubst Γ1 Γ3}
      -> ((σ1 σ⨾ σ2) σ≈ σ3)
      -> Tm {Γ1} (A [→] (B [ σ3 ]))
      -> Tm {Γ1} (A [→] ((B [ σ2 ]) [ σ1 ])))


    ([Ty]-var₀-subst-[▷] : ∀ {Γ} {σ : CtxSubst Γ Γ} {qΓ : Tm ([𝟙] [→] ([Ctx] [ σ ]))}
    -> Tm {Γ} ([𝟙] [→] ([Ty] var₀ [ σ [▷] qΓ ]))
    -> Tm {Γ} ([𝟙] [→] ([Ty] qΓ [ σ ])))


    ([CtxSubst] : ∀ {Γ1 Γ2 Γ3} {σ1 : CtxSubst Γ1 Γ2} {σ2 : CtxSubst Γ1 Γ3}
      -> Tm {Γ1} ([𝟙] [→] ([Ctx] [ σ1 ])) -> Tm {Γ1} ([𝟙] [→] ([Ctx] [ σ2 ])) -> Ty Γ1)
    ([quote-ctx-ty] : ∀ {A} {σ2 : CtxSubst ε A} {σ3 : CtxSubst _ ε}
      -> Tm {(ε , [Ctx]) , [Ty] var₀} ([𝟙] [→] ([CtxSubst] {σ1 = ισ} {σ2 = σ2} ⌜ ε ⌝c ⌜ (ε , [Ctx]) , [Ty] var₀ ⌝c [ σ3 ])))
    ([subst] : ∀ {Γ1 Γ2 Γ3}
      {σ1 : CtxSubst Γ1 Γ2} {σ2 : CtxSubst Γ1 Γ3}
      {qΓ1 : Tm {Γ1} ([𝟙] [→] ([Ctx] [ σ1 ]))} {qΓ2 : Tm {Γ1} ([𝟙] [→] ([Ctx] [ σ2 ]))}
      {σ3 : CtxSubst (Γ1 , [CtxSubst] qΓ1 qΓ2) Γ1}
      -> Tm {Γ1 , [CtxSubst] {σ1 = σ1} {σ2 = σ2} qΓ1 qΓ2 } (wk ([Ty] qΓ2) [→] (([Ty] qΓ1) [ σ3 ])))
    {-
    ([quote-ctx-ty]-[subst1] : ∀ {T : Ty (ε , [Σ] [Ctx] ([Ty] var₀Γ))} {qT : Tm {ε} ([𝟙] [→] [Σ] [Ctx] ([Ty] var₀Γ))} -> -- subst1 computes right
      ([dup] [⨾] ((⌜ T ⌝T [××] (qT [⨾] [quote-ctx-ty])) [⨾] [subst1]))
      Tm≈
      ⌜ T [ ισ, qT ] ⌝T)-}
    (if-fst-dec-eq-ctx_then_else_ : ∀ {Γ1 Γ2 Γ3 A} {σ1 : CtxSubst _ Γ2} {σ2 : CtxSubst _ Γ3}
      (qΓ        : Tm {Γ1}                       ([𝟙]               [→] ([Ctx] [ σ1 ])))
      (if-eq     : Tm {(Γ1 , [Ctx]) , [Ty] var₀} (wk (wk ([Ty] qΓ)) [→] (A [ σ2 ])))
      (if-not-eq : Tm {(Γ1 , [Ctx]) , [Ty] var₀} ([𝟙]               [→] (A [ σ2 ])))
      ->           Tm {(Γ1 , [Ctx]) , [Ty] var₀} ([𝟙]               [→] (A [ σ2 ])))
    (if-fst-dec-eq-ctx-true : ∀ {Γ1 Γ3 A σ1 σ2 qΓ qT if-eq if-not-eq}
      -> (((σ1 [▷] qΓ) [▷] qT) σ⨾ (σ2 [▷] if-fst-dec-eq-ctx_then_else_ {Γ1} {Γ1} {Γ3} {A} {σ1} {σ2} qΓ if-eq if-not-eq))
         σ≈
         ((((σ1 [▷] qΓ) [▷] qT) σ⨾ σ2) [▷] (map-unsubst [▷]-fst (map-unsubst [▷]-fst ([Ty]-var₀-subst-[▷] qT)) [⨾] if-eq)))
    (f : Ty (ε , [Ty] ⌜ ε ⌝c))
    where

    key : Tm {(ε , [Ctx]) , [Ty] var₀} ([𝟙] [→] ([Ty] {σ = ισ} ⌜ ε ⌝c [ (σε [▷] [quote-ctx-ty]) σ⨾ σε ]))
    key = if-fst-dec-eq-ctx ⌜ (ε , [Ctx]) , [Ty] var₀ ⌝c
          then map-wk2-ctx-subst ([quote-ctx-ty] {σ2 = ισ}) [⨾] [subst]
          else ⌜ [𝟙] ⌝T
    key-law : {T : Ty ((ε , [Ctx]) , [Ty] var₀)} ->
      (((ισ [▷] ⌜ (ε , [Ctx]) , [Ty] var₀ ⌝c) [▷] [Ty]-var₀-unsubst-[▷] ⌜ T ⌝T) σ⨾ (_ [▷] key))
      σ≈
      (ισ [▷] ⌜ introspect T ⌝T)
    key-law {T} = (((ισ [▷] ⌜ (ε , [Ctx]) , [Ty] var₀ ⌝c) [▷] [Ty]-var₀-unsubst-[▷] ⌜ T ⌝T) σ⨾ (_ [▷] key)) =[ if-fst-dec-eq-ctx-true ]=
      σ⨾₂ ((_ σ⨾ (_ σ⨾ σε)) [▷] (map-unsubst [▷]-fst (map-unsubst [▷]-fst ([Ty]-var₀-subst-[▷] ([Ty]-var₀-unsubst-[▷] ⌜ T ⌝T))) [⨾] (map-wk2-ctx-subst [quote-ctx-ty] [⨾] [subst])))
              =[ {!!} ]=
      σ⨾₂ ((ισ [▷] ⌜ T [ ((ισ [▷] ⌜ (ε , [Ctx]) , [Ty] var₀ ⌝c) [▷] [Ty]-var₀-unsubst-[▷] ⌜ T ⌝T) ] ⌝T)) =[ σι₂ ]=
      σ⨾₂ (ισ [▷] ⌜ introspect T ⌝T) [■]
{-
    key-law : {t : Ty (ε , [Σ] [Ctx] ([Ty] var₀Γ))} →
      ισ, (⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T) σ⨾
      (ισ,^ key)
      σ≈
      ισ, ⌜ t [ (ισ, (⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T)) ] ⌝T
    key-law {t} = (ισ, (⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T) σ⨾ (ισ,^ key)) =[ ισ,⨾ισ,^ ]=
      σ⨾₂ ισ, ((⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T) [⨾] key)               =[ ισ,′ if-fst-dec-eq-ctx-true ]=
      σ⨾₂ ισ,
            (([dup] [⨾]
              (⌜ t ⌝T [××]
               (⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T)))
             [⨾] (([ι] [××] [quote-ctx-ty]) [⨾] [subst1]))                                     =[ ισ,′ [⨾⨾] σ⨾₂ ισ,′ (_ [^⨾′] (([÷₂] [⨾⨾]) [⨾₂] ([××⨾] [⨾′^] _))) ]=
      σ⨾₂ ισ,
            ([dup] [⨾]
              (((⌜ t ⌝T [⨾] [ι])
                [××]
                ((⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T) [⨾] [quote-ctx-ty]))
               [⨾] [subst1]))                                                                  =[ ισ,′ (_ [^⨾′] (([⨾ι] [××′] [ι₂]) [⨾′^] _)) ]=
      σ⨾₂ ισ,
            ([dup] [⨾]
              ((⌜ t ⌝T
                [××]
                ((⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T) [⨾] [quote-ctx-ty]))
               [⨾] [subst1]))                                                                  =[ ισ,′ [quote-ctx-ty]-[subst1] ]=
      σ⨾₂ (ισ, ⌜ t [ (ισ, (⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ t ⌝T)) ] ⌝T)      [■]
-}
    private
      module loopy-conditions = loopy-setup.conditions
        (_ [▷] key)
        key-law
        f
    open loopy-conditions public using (t ; fixpt)
