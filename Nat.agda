open import Prelude

module Nat where
  data Nat : Set where
    Z : Nat
    1+ : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  -- equality of naturals is decidable. we represent this as computing a
  -- choice of units, with inl <> meaning that the naturals are indeed the
  -- same and inr <> that they are not.
  nateq : Nat → Nat → ⊤ + ⊤ -- yes + no
  nateq Z Z = Inl <>
  nateq Z (1+ m) = Inr <>
  nateq (1+ n) Z = Inr <>
  nateq (1+ n) (1+ m) = nateq n m
