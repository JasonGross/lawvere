open import Shim
open import Cat.Cartesian
open import Presheaf as _
open CartesianCat using (cat)
module loopy
  {l m n sl sm}
  (C : CartesianCat l m n)
  (A : Presheaf l m n sl sm (C .cat))
  where

private module C = CartesianCat C
private module A = Presheaf A
open C
open A using (_»_)

module setup
  {q} (Q : A.Run.Obj 𝟙 -> Type q)

  (a : C.Obj)
  (reflect : ∃[ a ∈ A.Run.Obj 𝟙 ] Q a -> 𝟙 ~> a)

  where

  module notations where
    chain : ∀ {a} {f g : A.Run.Obj a} -> f A.≈ g -> f A.≈ g
    chain x = x

    syntax chain {f = f} pf = f =[ pf ]=

    _[■] : ∀ {a} (f : A.Run.Obj a) -> f A.≈ f
    f [■] = A.ι₂
  open notations

  Fixpoint : A.Run.Obj a → Type (sl ⊔ sm ⊔ q)
  Fixpoint f = ∃[ xq ∈ ∃[ a ∈ A.Run.Obj 𝟙 ] Q a ] (fst xq A.≈ (reflect xq » f))

  module conditions₁
    (s : C.Obj)
    {p} (P : A.Run.Obj s -> Type p)

    (pack : ∃[ a ∈ A.Run.Obj s ] P a -> 𝟙 ~> s)
    (qual : ∀ ((t ▷ p) : ∃[ t ∈ A.Run.Obj s ] P t) -> Q (pack (t ▷ p) » t))
    where

    introspect : ∃[ a ∈ A.Run.Obj s ] P a -> ∃[ a ∈ A.Run.Obj 𝟙 ] Q a
    introspect (t ▷ p) = A.Map.run (pack (t ▷ p)) t ▷ qual (t ▷ p)

    module conditions₂
      (key : s ~> a)
      (key-law : ∀ {(t ▷ p) : ∃[ a ∈ A.Run.Obj s ] P a} -> (pack (t ▷ p) ⨾ key) ≈ reflect (introspect (t ▷ p)))

      (f : A.Run.Obj a)
      where

      t : A.Run.Obj s
      t = A.Map.run key f

      module theorem
        (p : P t)
        where

        fixpt : Fixpoint f
        fixpt = introspect (t ▷ p) ▷ proof
          module fixpt where
          proof : fst (introspect (t ▷ p)) A.≈ (reflect (introspect (t ▷ p)) » f)
          proof = fst (introspect (t ▷ p))             =[ A.ι₂ ]=
            A.⨾′ (pack (t ▷ p) » t)                    =[ A.ι₂ ]=
            A.⨾′ (pack (t ▷ p) » (key » f))            =[ A.Map-⨾.component _ _ _ ]=
            A.⨾′ ((pack (t ▷ p) ⨾ key) » f)            =[ A.Map′.component key-law _ ]=
            A.⨾′ ((reflect (introspect (t ▷ p))) » f)   [■]
