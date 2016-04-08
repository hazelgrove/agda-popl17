module Prelude where
  open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)

  -- empty type
  data ⊥ : Set where

  -- from false, derive whatever
  abort : ∀ {C : Set} → ⊥ → C
  abort ()

  -- unit
  data ⊤ : Set where
    <> : ⊤

  -- sums
  data _+_ (A B : Set) : Set where
    Inl : A → A + B
    Inr : B → A + B

  -- pairs
  infixr 1 _,_
  record Σ {l1 l2 : Level} (A : Set l1) (B : A → Set l2) : Set (lmax l1 l2) where
    constructor _,_
    field
      π1 : A
      π2 : B π1
  open Σ public

  syntax Σ A (\ x -> B) = Σ[ x ∈ A ] B

  _×_ : {l1 : Level} {l2 : Level} → (Set l1) → (Set l2) → Set (lmax l1 l2)
  A × B = Σ A λ _ → B

  infixr 1 _×_

  -- equality
  data _==_ {l : Level} {A : Set l} (M : A) : A → Set l where
    refl : M == M

  infixr 9 _==_

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL refl #-}

  _·_ : {l : Level} {α : Set l} {x y z : α} → x == y → y == z → x == z
  refl · refl = refl

  -- β: ! (refl m)  == refl m
  ! : {l : Level} {α : Set l} {x y : α} → x == y → y == x
  ! refl = refl

  -- β: (ap f (refl m)) == refl (f m)
  ap : {l1 l2 : Level} {α : Set l1} {β : Set l2} {x y : α} (F : α → β)
          → x == y → F x == F y
  ap F refl = refl

  -- β? : tr β (refl x) y == y
  tr : {l1 l2 : Level} {α : Set l1} {x y : α}
                    (B : α → Set l2)
                    → x == y
                    → B x
                    → B y
  tr B refl x₁ = x₁

  ap2 : {l1 l2 l3 : Level}
        {A : Set l1} {B : Set l2} {C : Set l3}
        {M N : A} {M' N' : B}
        (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  ap2 f refl refl = refl

  infix  2 _■
  infixr 2 _=<_>_

  _=<_>_ : {l : Level} {A : Set l} (x : A) {y z : A} → x == y → y == z → x == z
  _ =< p1 > p2 = p1 · p2

  _■ : {l : Level} {A : Set l} (x : A) → x == x
  _■ _ = refl

  -- options
  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  -- order
  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order
