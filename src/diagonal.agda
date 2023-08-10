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
  ; _⨾_ to _σ⨾_ ; _≈_ to _σ≈_ ; _⨾₂_ to _σ⨾₂_ ; ι₂ to σι₂)
open TyCat.Run using () renaming (Obj to Ty)
open TyCat.Map using () renaming (run to subst)
_[_] : ∀ {Γ Γ′} -> Ty Γ′ -> CtxSubst Γ Γ′ -> Ty Γ
T [ σ ] = subst σ T

import singleton CtxCat TyCat as loopy

module setup
  {tm} (Tm : ∀ {Γ} -> Ty Γ -> Type tm)
  (_,_ : ∀ (Γ : Ctx) (T : Ty Γ) -> Ctx)
  ([𝟙] : ∀ {Γ} -> Ty Γ)
  (_[→]_ : ∀ {Γ} (A B : Ty Γ) -> Ty Γ)
  ([Ctx] : ∀ {Γ} -> Ty Γ)
  ([Ty] : ∀ {Γ} -> Tm {Γ} ([𝟙] [→] [Ctx]) -> Ty Γ)
  ([Tm] : ∀ {Γ} {[Γ] : Tm {Γ} ([𝟙] [→] [Ctx])} -> Tm {Γ} ([𝟙] [→] [Ty] [Γ]) -> Ty Γ)
  ([Σ] : ∀ {Γ} -> (A : Ty Γ) -> (B : Ty (Γ , A)) -> Ty Γ)
  ([Π] : ∀ {Γ} -> (A : Ty Γ) -> (B : Ty (Γ , A)) -> Ty Γ)
  (⌜_⌝c : ∀ {Γ} -> (Γ′ : Ctx) -> Tm {Γ} ([𝟙] [→] [Ctx]))
  (⌜_⌝T : ∀ {Γ Γ′} -> (T : Ty Γ) -> Tm {Γ′} ([𝟙] [→] [Ty] ⌜ Γ ⌝c))
  (_σ,_ : ∀ {Γ Γ′} (σ : CtxSubst Γ Γ′) {T′ : Ty Γ′}
    -> Tm {Γ} (([𝟙] {Γ}) [→] (T′ [ σ ])) -> CtxSubst Γ (Γ′ , T′))
  (ισ, : ∀ {Γ} {T : Ty Γ} -> Tm {Γ} ([𝟙] [→] T) -> CtxSubst Γ (Γ , T))
  -- TODO: naming???
  (ισ,^ : ∀ {Γ} {A B : Ty Γ} -> Tm {Γ} (A [→] B) -> CtxSubst (Γ , A) (Γ , B))
  (var₀Γ : ∀ {Γ} -> Tm {Γ , [Ctx]} ([𝟙] [→] [Ctx]))
  (_[▷]_ : ∀ {Γ Z A B} -> (a : Tm {Γ} (Z [→] A)) -> Tm {Γ} ([Π] Z ([𝟙] [→] (B [ ισ,^ a ]))) -> Tm {Γ} (Z [→] [Σ] A B))
  -- TODO: better factorization of reduction?
  (constΠ-subst : ∀ {Γ qΓ} -> Tm {Γ} ([𝟙] [→] [Ty] qΓ) -> Tm {Γ} ([Π] [𝟙] ([𝟙] [→] ([Ty] var₀Γ [ ισ,^ qΓ ]))))
  where

  private
    module loopy-setup = loopy.setup
      (ε , [Ty] ⌜ ε ⌝c)
      (λ{ T -> ισ, ⌜ T ⌝T })
      (ε , [Σ] [Ctx] ([Ty] var₀Γ))
      (λ{ T -> ισ, (⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c [▷] constΠ-subst ⌜ T ⌝T) })
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
    (_[×]_ : ∀ {Γ} -> Ty Γ -> Ty Γ -> Ty Γ)
    ([*] : ∀ {Γ A} -> Tm {Γ} (A [→] [𝟙]))
    (_[⨾]_ : ∀ {Γ A B C} -> Tm {Γ} (A [→] B) -> Tm {Γ} (B [→] C) -> Tm {Γ} (A [→] C))
    ([⨾⨾] : ∀ {Γ A B C D} {f : Tm {Γ} (A [→] B)} {g : Tm {Γ} (B [→] C)} {h : Tm {Γ} (C [→] D)} -> ((f [⨾] g) [⨾] h) Tm≈ (f [⨾] (g [⨾] h)))
    (_[××]_ : ∀ {Γ A B A′ B′} -> Tm {Γ} (A [→] A′) -> Tm {Γ} (B [→] B′) -> Tm {Γ} ((A [×] B) [→] (A′ [×] B′)))
    (_[^⨾′]_ : ∀ {Γ} {A B C : Ty Γ} (f : Tm (A [→] B)) {g g′ : Tm (B [→] C)} -> g Tm≈ g′ -> (f [⨾] g) Tm≈ (f [⨾] g′))
    (_[⨾′^]_ : ∀ {Γ} {A B C : Ty Γ} {f f′ : Tm (A [→] B)} -> f Tm≈ f′ -> (g : Tm (B [→] C)) -> (f [⨾] g) Tm≈ (f′ [⨾] g))
    ([÷₂]_ : ∀ {Γ A} {f f′ : Tm {Γ} A} -> f Tm≈ f′ -> f′ Tm≈ f)
    (_[⨾₂]_ : ∀ {Γ A} {f g h : Tm {Γ} A} -> f Tm≈ g -> g Tm≈ h -> f Tm≈ h)
    ([××⨾] : ∀ {Γ} {a1 a2 a3 a1′ a2′ a3′ : Ty Γ} {f : Tm (a1 [→] a2)} {g : Tm (a2 [→] a3)} {f′ : Tm (a1′ [→] a2′)} {g′ : Tm (a2′ [→] a3′)}
                 -> ((f [××] f′) [⨾] (g [××] g′)) Tm≈ ((f [⨾] g) [××] (f′ [⨾] g′)))
    (_[××′]_ : ∀ {Γ} {a1 a2 a1′ a2′ : Ty Γ} {f g : Tm (a1 [→] a2)} {f′ g′ : Tm (a1′ [→] a2′)} -> f Tm≈ g -> f′ Tm≈ g′ -> (f [××] f′) Tm≈ (g [××] g′))
    ([dup] : ∀ {Γ A} -> Tm {Γ} (A [→] (A [×] A)))
    ([ι] : ∀ {Γ A} -> Tm {Γ} (A [→] A))
    ([⨾ι] : ∀ {Γ} {a1 a2 : Ty Γ} {f : Tm (a1 [→] a2)} -> (f [⨾] [ι]) Tm≈ f)
    ([ι₂] : ∀ {Γ T} {f : Tm {Γ} T} -> f Tm≈ f)
    (ισ,⨾ισ,^ : ∀ {Γ} {A B : Ty Γ} {f : Tm {Γ} ([𝟙] [→] A)} {g : Tm {Γ} (A [→] B)}
      -> ((ισ, f) σ⨾ (ισ,^ g)) σ≈ (ισ, (f [⨾] g)))
    (ισ,′ : ∀ {Γ T} {t1 t2 : Tm {Γ} ([𝟙] [→] T)} -> t1 Tm≈ t2 -> ισ, t1 σ≈ ισ, t2)

    ([quote-ctx-ty] : Tm {ε} ([Σ] [Ctx] ([Ty] var₀Γ) [→] [Tm] ⌜ [Σ] {ε} [Ctx] ([Ty] var₀Γ) ⌝T))
    ([subst1] : ∀ {Γ Γ′ T} -> Tm {Γ} (([Ty] ⌜ Γ′ , T ⌝c [×] [Tm] ⌜ T ⌝T) [→] [Ty] ⌜ Γ′ ⌝c))
    ([quote-ctx-ty]-[subst1] : ∀ {T : Ty (ε , [Σ] [Ctx] ([Ty] var₀Γ))} {qT : Tm {ε} ([𝟙] [→] [Σ] [Ctx] ([Ty] var₀Γ))} -> -- subst1 computes right
      ([dup] [⨾] ((⌜ T ⌝T [××] (qT [⨾] [quote-ctx-ty])) [⨾] [subst1]))
      Tm≈
      ⌜ T [ ισ, qT ] ⌝T)
    (if-fst-dec-eq-ctx_then_else_ : ∀ {Γ A} (qΓ : Tm {Γ} ([𝟙] [→] [Ctx]))
      (if-eq : Tm {Γ} ((([Ty] qΓ) [×] ([Σ] [Ctx] ([Ty] var₀Γ))) [→] A))
      (if-not-eq : Tm {Γ} ([Σ] [Ctx] ([Ty] var₀Γ) [→] A))
      -> Tm {Γ} ([Σ] [Ctx] ([Ty] var₀Γ) [→] A))
    (if-fst-dec-eq-ctx-true : ∀ {Γ A qΓ if-eq if-not-eq snd} -> -- if the first components are equal
      ((qΓ [▷] constΠ-subst snd) [⨾] if-fst-dec-eq-ctx_then_else_ {Γ} {A} qΓ if-eq if-not-eq)
      Tm≈ (([dup] [⨾] (snd [××] (qΓ [▷] constΠ-subst snd))) [⨾] if-eq))
    (f : Ty (ε , [Ty] ⌜ ε ⌝c))
    where

    key : Tm ([Σ] [Ctx] ([Ty] var₀Γ) [→] [Ty] ⌜ ε ⌝c)
    key = if-fst-dec-eq-ctx ⌜ ε , [Σ] [Ctx] ([Ty] var₀Γ) ⌝c
          then ([ι] [××] [quote-ctx-ty]) [⨾] [subst1]
          else ([*] [⨾] ⌜ [𝟙] ⌝T)

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

    private
      module loopy-conditions = loopy-setup.conditions
        (ισ,^ key)
        key-law
        f
    open loopy-conditions public using (t ; fixpt)
