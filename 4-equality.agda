module 4-equality where

-- Equality definition In the book there is the following definiton using
-- parameterized data type.
--
-- The definition features an asymmetry, in that the first argument to _≡_ is
-- given by the parameter x : A, while the second is given by an index in A →
-- Set. This follows our policy of using parameters wherever possible. The first
-- argument to _≡_ can be a parameter because it doesn’t vary, while the second
-- must be an index, so it can be required to be equal to the first.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- It is however also possible to define it using just indexed data types

data _≡≡_ : {A : Set} → A → A → Set where
  refl-≡≡ : ∀ {A : Set} → ∀ {x : A} → x ≡≡ x

-- the refl definition is the same as this one:
-- refl : ∀ {A : Set} → (x : A) -> x ≡ x

infix 4 _≡_

-- We set the precedence of _≡_ at level 4, the same as _≤_, which means it
-- binds less tightly than any arithmetic operator. It associates neither to
-- left nor right; writing x ≡ y ≡ z is illegal.

--
-- SYMETRY
--

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  -------
  → y ≡ x
 
-- I could start by introducing a variable for x≡y and then case splitting on it
-- that gives me refl and the obvious solution to that is refl
sym refl = refl


--
-- TRANSITIVITY
--

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  -------
  → x ≡ z

trans refl refl = refl

--
-- CONGURENCE
--

-- Equality satisfies congruence. If two terms are equal, they remain so after
-- the same function is applied to both:

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  -----------
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {a b : A} {c d : B}
  → a ≡ b
  → c ≡ d
  ---------------
  → f a c ≡ f b d
cong₂ f refl refl = refl

-- Equality is also a congruence in the function position of an application. If
-- two functions are equal, then applying them to the same term yields equal
-- terms:

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

--
-- SUBSTITUTION
--

-- If two values are equal and a predicate holds of the first then it also holds
-- of the second:

subs : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  -------
  → P x
  → P y

subs p refl px = px

--
-- REASONING
--

-- a module can define explicit and implicit parameters
-- definitions must be indented
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y = x≡y

  -- _≡⟨⟩_ is equivalent to _≡⟨ refl ⟩_
  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  = refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  -------
  → x ≡ z

trans′ {A} {x} {y} {z} xy yz = begin
  x
  ≡⟨ xy ⟩
  y
  ≡⟨ yz ⟩
  z
  ∎

-- the above parses as following: begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))
-- after simplification: trans x≡y (trans y≡z refl)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = begin
  n
  ≡⟨ sym (+-identity n) ⟩
  n + zero
  ∎

+-comm (suc m) n = begin
  (suc m + n)
  ≡⟨⟩
  suc (m + n)
  ≡⟨ sym (+-suc m n) ⟩
  (m + suc n)
  ≡⟨ +-comm m (suc n) ⟩
  suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
  (n + suc m)
  ∎

-- above I forgot congurance, here it is
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero = begin
  (m + zero)
  ≡⟨ +-identity m ⟩
  m
  ≡⟨⟩
  zero + m
  ∎
+-comm′ m (suc n) = begin
  (m + suc n)
  ≡⟨ +-suc m n ⟩
  suc (m + n)
  ≡⟨ cong suc (+-comm′ m n) ⟩
  suc (n + m)
  ≡⟨⟩
  (suc n + m)
  ∎

{- Exercise ≤-Reasoning (stretch)

The proof of monotonicity from Chapter Relations can be written in a more
readable form by using an analogue of our notation for ≡-Reasoning. Define
≤-Reasoning analogously, and use it to write out an alternative proof that
addition is monotonic with regard to inequality. Rewrite all of +-monoˡ-≤,
+-monoʳ-≤, and +-mono-≤. -}

module ≤-Reasoning where

  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ}
      --------
      → zero ≤ n

    s≤s : ∀ {m n : ℕ}
      → m ≤ n
      -------------
      → suc m ≤ suc n

  infix 4 _≤_

  postulate
    ≤-refl : ∀ {n : ℕ}
      -------
      → n ≤ n

    ≤-trans : ∀ {m n p : ℕ}
      → m ≤ n
      → n ≤ p
      -------
      → m ≤ p

  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≤-≡⟨_⟩_
  infix  3 _≤-∎

  ≤-begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  ≤-begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≤-≡⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≡ y
    → y ≤ z
    -------
    → x ≤ z
  x ≤-≡⟨ refl ⟩ y≤z = y≤z

  _≤-∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ≤-∎ = ≤-refl

open ≤-Reasoning

-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q

+-monoʳ-≤ zero p q p≤q = ≤-begin
  (zero + p)
  ≤⟨⟩
  p
  ≤⟨ p≤q ⟩
  q
  ≤⟨⟩
  zero + q
  ≤-∎

+-monoʳ-≤ (suc n) p q p≤q = ≤-begin
  (suc n) + p
  ≤⟨⟩
  suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
  (suc n + q)
  ≤⟨⟩
  (suc n) + q
  ≤-∎

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n = ≤-begin
  m + p
  ≤-≡⟨ +-comm m p ⟩
  p + m
  ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
  p + n
  ≤-≡⟨ +-comm p n ⟩
  n + p
  ≤-∎

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  -------
  → m + p ≤ n + q

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- or a much longer way :-(

+-mono-l-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p

+-mono-l-≤ m n zero m≤n = ≤-begin
  m + zero
  ≤-≡⟨ +-comm m zero ⟩
  zero + m
  ≤⟨⟩
  m
  ≤⟨ m≤n ⟩
  n
  ≤⟨⟩
  zero + n
  ≤-≡⟨ +-comm zero n ⟩
  n + zero
  ≤-∎

+-mono-l-≤ m n (suc p) m≤n = ≤-begin
  (m + suc p)
  ≤-≡⟨ +-comm m (suc p) ⟩
  suc (p + m)
  ≤-≡⟨ cong suc (+-comm p m) ⟩
  suc (m + p)
  ≤⟨ s≤s (+-mono-l-≤ m n p m≤n) ⟩
  suc (n + p)
  ≤-≡⟨ cong suc (+-comm n p) ⟩
  suc (p + n)
  ≤⟨⟩
  (suc p) + n
  ≤-≡⟨ +-comm (suc p) n ⟩
  (n + suc p)
  ≤-∎


--
-- REWRITING
--

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
    -------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
    --------
    → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)

even-comm m n ev rewrite +-comm m n = ev

+-comm″ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm″ zero n rewrite +-identity n = refl
+-comm″ (suc m) n rewrite +-suc n m | +-comm″ m n = refl

-- rewrite is a shorthand for with


even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

-- In general, one can follow with by any number of expressions, separated by
-- bars, where each following equation has the same number of patterns. We often
-- write expressions and the corresponding patterns so they line up in columns,
-- as above. Here the first column asserts that m + n and n + m are identical,
-- and the second column justifies that assertion with evidence of the
-- appropriate equality. Note also the use of the dot pattern, .(n + m). A dot
-- pattern consists of a dot followed by an expression, and is used when other
-- information forces the value matched to be equal to the value of the
-- expression in the dot pattern. In this case, the identification of m + n and
-- n + m is justified by the subsequent matching of +-comm m n against refl. One
-- might think that the first clause is redundant as the information is inherent
-- in the second clause, but in fact Agda is rather picky on this point:
-- omitting the first clause or reversing the order of the clauses will cause
-- Agda to report an error.

even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n  =  subs even (+-comm m n)

--
-- LEIBNIZ EQUALITY
--

-- almost all is comming from the PLFA book, here it is so I have a reference

-- The form of asserting equality that we have used is due to Martin Löf, and
-- was published in 1975. An older form is due to Leibniz, and was published in
-- 1686. Leibniz asserted the identity of indiscernibles: two objects are equal
-- if and only if they satisfy the same properties. This principle sometimes
-- goes by the name Leibniz’ Law, and is closely related to Spock’s Law, “A
-- difference that makes no difference is no difference”. Here we define Leibniz
-- equality, and show that two terms satisfy Leibniz equality if and only if
-- they satisfy Martin Löf equality.

-- Leibniz equality is usually formalised to state that x ≐ y holds if every
-- property P that holds of x also holds of y. Perhaps surprisingly, this
-- definition is sufficient to also ensure the converse, that every property P
-- that holds of y also holds of x.

-- Let x and y be objects of type A. We say that x ≐ y holds if for every
-- predicate P over type A we have that P x implies P y:

_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
-- refl-≐ P Px = Px
refl-≐ P Px = Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

-- Given x ≐ y, a specific P, we have to construct a proof that P y implies P x.
-- To do so, we instantiate the equality with a predicate Q such that Q z holds
-- if P z implies P x. The property Q x is trivial by reflexivity, and hence Q y
-- follows from x ≐ y. But Q y is exactly a proof of what we require, that P y
-- implies P x.

-- We now show that Martin Löf equality implies Leibniz equality, and vice
-- versa. In the forward direction, if we know x ≡ y we need for any P to take
-- evidence of P x to evidence of P y, which is easy since equality of x and y
-- implies that any proof of P x is also a proof of P y:

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P = subs P x≡y

-- This direction follows from substitution, which we showed earlier.

-- In the reverse direction, given that for any P we can take a proof of P x to
-- a proof of P y we need to show x ≡ y:

≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-- The proof is similar to that for symmetry of Leibniz equality. We take Q to
-- be the predicate that holds of z if x ≡ z. Then Q x is trivial by reflexivity
-- of Martin Löf equality, and hence Q y follows from x ≐ y. But Q y is exactly
-- a proof of what we require, that x ≡ y.

--
-- UNIVERSE POLYMORPHISM
--

-- As we have seen, not every type belongs to Set, but instead every type
-- belongs somewhere in the hierarchy Set₀, Set₁, Set₂, and so on, where Set
-- abbreviates Set₀, and Set₀ : Set₁, Set₁ : Set₂, and so on. The definition of
-- equality given above is fine if we want to compare two values of a type that
-- belongs to Set, but what if we want to compare two values of a type that
-- belongs to Set ℓ for some arbitrary level ℓ?

-- The answer is universe polymorphism, where a definition is made with respect
-- to an arbitrary level ℓ. To make use of levels, we first import the
-- following:

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

-- We rename constructors zero and suc to lzero and lsuc to avoid confusion
-- between levels and naturals.

-- Levels are isomorphic to natural numbers, and have similar constructors:
-- lzero : Level
-- lsuc  : Level → Level

-- The names Set₀, Set₁, Set₂, and so on, are abbreviations for
-- Set lzero
-- Set (lsuc lzero)
-- Set (lsuc (lsuc lzero))

-- and so on. There is also an operator
-- _⊔_ : Level → Level → Level
--that given two levels returns the larger of the two.

-- Here is the definition of equality, generalised to an arbitrary level:

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

-- Similarly, here is the generalised definition of symmetry:

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′

-- For simplicity, we avoid universe polymorphism in the definitions given in the text, but most definitions in the standard library, including those for equality, are generalised to arbitrary levels as above.

-- Here is the generalised definition of Leibniz equality:

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

-- Before the signature used Set₁ as the type of a term that includes Set, whereas here the signature uses Set (lsuc ℓ) as the type of a term that includes Set ℓ.

-- Most other functions in the standard library are also generalised to arbitrary levels. For instance, here is the definition of composition.

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)
