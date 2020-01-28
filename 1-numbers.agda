-- a module definition
module 1-numbers where

-- data definition
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{- Importing number so we can type 1 instead of suc zero.
   This is also an example of a multiline comment -}

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

----------------------------------------
-- ADDITION
----------------------------------------

{- recursive definition: larger numbers are defined in terms of addition of
smaller numbers, a well founded definition. -}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 1 + 1 ≡ 2
_ =
  begin
    1 + 1
  ≡⟨⟩
    2
  ∎

_ : 1 + 1 ≡ 2
_ = refl

----------------------------------------
-- MULTIPLICATION
----------------------------------------

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

_ : 3 * 4 ≡ 12
_ = refl


----------------------------------------
-- EXPONENTIATION
----------------------------------------

_^_ : ℕ → ℕ → ℕ
m ^ zero    =  1
m ^ (suc n)  =  m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = refl


----------------------------------------
-- MONUS
----------------------------------------

_∸_ : ℕ → ℕ → ℕ
m ∸ zero  =  m
zero ∸ _ =  zero
suc m ∸ suc n  =  m ∸ n

_ : 3 ∸ 2 ≡ 1
_ = refl

-- _ : 3 ∸ 5 ≡ 0
-- _ = refl

_ : 3 ∸ 5 ≡ 0
_ =
  begin
  3 ∸ 5
  ≡⟨⟩
  2 ∸ 4
  ≡⟨⟩
  1 ∸ 3
  ≡⟨⟩
  0 ∸ 2
  ≡⟨⟩
  0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

_ : _∸_ (_∸_ 3 5) 10 ≡ 0
_ = refl

----------------------------------------
-- BIN
----------------------------------------

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

eleven = ⟨⟩ I O I I
twelve = ⟨⟩ I I O O

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

_ : inc eleven ≡ twelve
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

_ : to 11 ≡ eleven
_ = refl

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = 2 * from m
from (m I) = 1 + 2 * from m

_ : from eleven ≡ 11
_ = refl

data _even : ℕ -> Set where
      ZERO : zero even
      -- STEP : (x : ℕ) → x even → suc (suc x) even
      STEP : ∀ x → x even → suc (suc x) even

_ : 4 even
_ = STEP 2 (STEP 0 ZERO)
