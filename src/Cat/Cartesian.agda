open import Shim
module Cat.Cartesian l m n where
open import Cat l m n

record IsCartesian (C : Cat) : Type (l ⊔ m ⊔ n) where
  private module C = Cat C
  open C
  field 𝟙     : Obj
  field _×_   : Obj -> Obj -> Obj
  infix 9 _×_

  field *     : ∀ {a} -> (a ~> 𝟙)
  field dup   : ∀ {a} -> a ~> (a × a)

  field _××_  : ∀ {a b c d} -> a ~> c -> b ~> d -> (a × b) ~> (c × d)
  infix 9 _××_

  -- these two not strictly necessary
  field getl  : ∀ {a b} -> (a × b) ~> a
  field getr  : ∀ {a b} -> (a × b) ~> b

  field *′ : ∀ {a} {f g : a ~> 𝟙} -> f ≈ g
  field ××ι  : ∀ {a1 a2} -> (ι {a1} ×× ι {a2}) ≈ ι
  field dup-getl : ∀ {a} -> (dup {a} ⨾ getl) ≈ ι
  field dup-getr : ∀ {a} -> (dup {a} ⨾ getr) ≈ ι
  field ××⨾ : ∀ {a1 a2 a3 a1′ a2′ a3′} {f : a1 ~> a2} {g : a2 ~> a3} {f′ : a1′ ~> a2′} {g′ : a2′ ~> a3′}
                 -> ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′))
  field dup⨾ : ∀ {a1 a2} {f : a1 ~> a2} -> (f ⨾ dup) ≈ (dup ⨾ (f ×× f))
  field getl⨾ : ∀ {a1 a2 a1′ a2′} {f : a1 ~> a2} {f′ : a1′ ~> a2′}
                   -> ((f ×× f′) ⨾ getl) ≈ (getl ⨾ f)
  field getr⨾ : ∀ {a1 a2 a1′ a2′} {f : a1 ~> a2} {f′ : a1′ ~> a2′}
                   -> ((f ×× f′) ⨾ getr) ≈ (getr ⨾ f′)
  field _××′_ : ∀ {a1 a2 a1′ a2′} {f g : a1 ~> a2} {f′ g′ : a1′ ~> a2′} -> f ≈ g -> f′ ≈ g′ -> (f ×× f′) ≈ (g ×× g′)
  infix 9 _××′_

  _^××′_ : ∀ {a1 a2 a1′ a2′} (f : a1 ~> a2) {f′ g′ : a1′ ~> a2′} -> f′ ≈ g′ -> (f ×× f′) ≈ (f ×× g′)
  f ^××′ e = ι₂ ××′ e
  infixr 9 _^××′_

  _××′^_ : ∀ {a1 a2 a1′ a2′} {f g : a1 ~> a2} -> f ≈ g -> (f′ : a1′ ~> a2′) -> (f ×× f′) ≈ (g ×× f′)
  e ××′^ f′ = e ××′ ι₂
  infixl 9 _××′^_

record IsClosed (C : Cat) (CC : IsCartesian C) : Type (l ⊔ m ⊔ n) where
  private module C = Cat C
  private module CC = IsCartesian CC
  open C
  open CC

  field _^_ : Obj -> Obj -> Obj
  field apply : ∀ {a b : Obj} -> (((b ^ a) × a) ~> b)
  -- TODO: more systematic?
  field lambda : ∀ {a b : Obj} -> (a ~> b) -> (𝟙 ~> (b ^ a))
  field lambda-apply : ∀ {a b c : Obj} {f : a ~> b} {g : c ~> a} -> ((lambda f ×× g) ⨾ apply) ≈ ((getr ⨾ g) ⨾ f)
--  field uncurry : ∀ {a b : Obj} ->
  -- TODO: more fields

record CartesianCat : Type (lsuc (l ⊔ m ⊔ n)) where
  field cat : Cat
  field cc : IsCartesian cat
  private module cat = Cat cat
  private module cc = IsCartesian cc
  open cat public
  open cc public

record CartesianClosedCat : Type (lsuc (l ⊔ m ⊔ n)) where
  field cat : Cat
  field cc : IsCartesian cat
  field ccc : IsClosed cat cc
  ccat : CartesianCat
  ccat = record { cat = cat ; cc = cc }
  private module cat = Cat cat
  private module cc = IsCartesian cc
  private module ccc = IsClosed ccc
  open cat public
  open cc public
  open ccc public
