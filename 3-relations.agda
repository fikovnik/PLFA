module 3-relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

data _≤_ : ℕ → ℕ → Set where

  -- Base case:
  -- - for all naturals n, the proposition zero ≤ n holds.
  -- - for all naturals n, the constructor z≤n produces evidence that zero ≤ n
  --   holds.

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  -- Inductive case:
  -- - for all naturals m and n, if the proposition m ≤ n holds,
  --   then the proposition suc m ≤ suc n holds.
  -- - for all naturals m and n, the constructor s≤s takes evidence that m ≤ n
  --   holds into evidence that suc m ≤ suc n holds.

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

-- The z≤n and s≤s are constructor names. The zero ≤ n, m ≤ n and suc m ≤ suc n
-- are types, concretely, indexed data types (e.g. index by two naturals m and
-- n). The trick with the dashed line in the inference rules is just a comment
-- actually.

-- define precedence at level 4, so it binds less tightly
-- than _+_ at level 6 and hence `1 + 2 ≤ 3` parses as `(1 + 2) ≤ 3`.

infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- The s≤s and z≤n are defined using implicit arguments (in between {}).
-- Their values are inferred.
-- They can also be passed explicitly

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- The can be named

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

-- Some can be left out, yet the possition is fixed.

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

{- Manual proof:

  z≤n -----
      0 ≤ 2
 s≤s -------
      1 ≤ 3
s≤s ---------
      2 ≤ 4   -}

--
-- INVERSION
--

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl


--
-- PROPERTIES OF RELATIONS
--

{-     Reflexive: ∀ n, the relation n ≤ n holds (each element is comparable to itself).
      Transitive: ∀ m, n, and p, if m ≤ n and n ≤ p hold, then m ≤ p holds (the start of a chain of precedence relations must precede the end of the chain).
  Anti-symmetric: ∀ m and n, if both m ≤ n and n ≤ m hold, then m ≡ n holds (no two different elements precede each other).
           Total: ∀ m and n, either m ≤ n or n ≤ m holds (or both if m ≡ n).

        Preorder: any relation that is reflexive and transitive.
   Partial order: any preorder that is also anti-symmetric.
     Total order: any partial order that is also total. -}

{- Exercise orderings (practice)

Give an example of a preorder that is not a partial order.

The size of a set |S|:
A relation ≤:
  S1 ≤ S2 iff |S1| ≤ |S2| which is reflexive and transitive, but not anti-symetric as
  S1 and S2 can be different but have the same size.

Give an example of a partial order that is not a total order.

Subsets S = {a,b} are {∅, {a, b}, {a}, {b}}
The subset ⊂ is partial order:

A ⊂ A                  -- reflexivity
A ⊂ B ∧ B ⊂ C ⇒ A ⊂ C  -- transitivity
A ⊂ B ∧ B ⊂ A ⇒ A ≡ B  -- anti-symetricity

It does not satisfy the totality:

{0} ⊄ {1} ∧ {1} ⊄ {0} -}

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
-- ≤-refl {suc n} = s≤s {n} {n} (≤-refl {n})

data _<=_ : ℕ → ℕ → Set where
  z<=n : ∀ (n : ℕ)
    -----------
    → zero <= n

  s<=s : ∀ (m n : ℕ)
    → m <= n
    ----------------
    → suc m <= suc n

_ : 2 <= 4
_ = s<=s 1 3 (s<=s zero 2 (z<=n 2))

<=-refl : ∀ (n : ℕ) → n <= n
<=-refl zero = z<=n zero
<=-refl (suc n) = s<=s n n (<=-refl n)

≤-trans : ∀ {n m p : ℕ}
  → m ≤ n
  → n ≤ p
  ---------------
  → m ≤ p

{- I started with ≤-trans e1 e2 and did a split on both variables. The first two
cases are the same - they are defined using z≤n so they can be merged together.
The last one can be done interactivelly using C-c C-r. -}

≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- the same, but using the non-implicit version
<=-trans : ∀ (m n p : ℕ)
  → m <= n
  → n <= p
    -----
  → m <= p

<=-trans .0 n p (z<=n .n) e2 = z<=n p
<=-trans .(suc m) .(suc n) .(suc p) (s<=s m n e1) (s<=s n p e2) = s<=s m p (<=-trans m n p e1 e2)

≤-antisym : ∀ { m n : ℕ }
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s e1) (s≤s e2) = cong suc (≤-antisym e1 e2)


{- Exercise ≤-antisym-cases (practice)

The above proof omits cases where one argument is z≤n and one argument is s≤s. Why is it ok to omit them? -}

-- This is how it would look like:
-- ≤-antisym z≤n (s≤s e1) = ?
-- m ≡ n, n ≡ zero from the z≤n and so it is required than m ≡ zero, but putting there s≤s is like saying that suc n ≡ zero

<=-antisym : ∀ (m n : ℕ)
  → m <= n
  → n <= m
    -----
  → m ≡ n
<=-antisym .0 .0 (z<=n .0) (z<=n .0) = refl
<=-antisym .(suc m) .(suc n) (s<=s m n e1) (s<=s .n .m e2) = cong suc (<=-antisym m n e1 e2)

--
-- TOTAL ORDER
--

{- The fourth property to prove about comparison is that it is total: for any
naturals m and n either m ≤ n or n ≤ m, or both if m and n are equal -}

-- A data type with parameters (m n) each of these parameters will translate to
-- an implicit paramter for the constructors. Parameterised declarations are
-- shorter, easier to read, and occasionally aid Agda’s termination checker, so
-- we will use them in preference to indexed types when possible

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

{- Evidence that Total m n holds is either of the form forward m≤n or flipped
n≤m, where m≤n and n≤m are evidence of m ≤ n and n ≤ m respectively. -}

-- an equivalence using indexed data type
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n

-- totality specificaton
≤-total : ∀ (m n : ℕ) → Total m n

-- base case: z≤n is an evidence that for zero ≤ n needed for forward
≤-total zero n = forward z≤n

-- base case: z≤n is an evidence that for zero ≤ (suc n) needed for flipped
-- which flips the m and n in the type
≤-total (suc m) zero = flipped z≤n

-- inductive case, inductive hypothesis ≤-total m n establishes with:
≤-total (suc m) (suc n) with ≤-total m n
       -- m≤n as evidence that m ≤ n, from which it follows that the forward case of
       -- the proposition holds with s≤s m≤n as evidence that suc m ≤ suc n.
...  | forward m≤n = forward (s≤s m≤n)
       -- n≤m as evidence that n ≤ m, from which it follows that the flipped case of
       -- the proposition holds with s≤s n≤m as evidence that suc n ≤ suc m.
...  | flipped n≤m = flipped (s≤s n≤m)

{- To really get how this works, it is the best to go step by step
interactivelly. Even the helper can be done interactivelly, one just needs to
define its type which is clear from the hole goals. Note that the definitions
after where *must* be indented. -}

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  = helper (≤-total′ m n) where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)

--
-- MONOTONICITY
--

-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

-- case of showing addition is monotonic on the right (right form the _+_)
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q

-- Base case: The first argument is zero in which case zero + p ≤ zero + q
-- simplifies to p ≤ q, the evidence for which is given by the argument p≤q.
+-monoʳ-≤ zero p q p≤q = p≤q

-- Inductive case: The first argument is suc n, in which case suc n + p ≤ suc n
-- + q simplifies to suc (n + p) ≤ suc (n + q). The inductive hypothesis
-- +-monoʳ-≤ n p q p≤q establishes that n + p ≤ n + q, and our goal follows by
-- applying s≤s.
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

-- case of showing addition is monotonic on the left (from the _+_)
+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n
  rewrite                 -- m + p ≤ n + p
    +-comm m p            -- p + m ≤ n + p
  | +-comm n p            -- p + m ≤ p + n
  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q

-- invoking +-monoˡ-≤ m n p m≤n proves m + p ≤ n + p and
-- invoking +-monoʳ-≤ n p q p≤q proves n + p ≤ n + q, and
-- combining these with transitivity proves m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

{- Exercise *-mono-≤ (stretch)

Show that multiplication is monotonic with regard to inequality. -}

-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m * p ≤ n * q

*-mono-≤ : ∀ (m n p q : ℕ)
   → m ≤ n
   → p ≤ q
     -------------
   → m * p ≤ n * q

*-mono-≤ zero zero p q m≤n p≤q = z≤n
*-mono-≤ zero (suc n) p q m≤n p≤q = z≤n
*-mono-≤ (suc m) (suc n) p q m≤n p≤q = -- p + m * p ≤ q + n * q
  +-mono-≤ p q (m * p) (n * q) p≤q (*-mono-≤ m n p q (inv-s≤s m≤n) p≤q)


--
-- STRICT INEQUALITY
--

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- _<_ is not reflexive, but it is irreflexive and trichotom and transitive

{- Exercise <-trans (recommended)

Show that strict inequality is transitive. -}

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p

<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

{- Exercise trichotomy (practice)

Show that strict inequality satisfies a weak version of trichotomy, in the sense that for any m and n that one of the following holds:

    m < n,
    m ≡ n, or
    m > n.

Define m > n to be the same as n < m. You will need a suitable data declaration, similar to that used for totality. -}

data Trichotomy (m n : ℕ) : Set where

  lt :
      m < n
      ---------
    → Trichotomy m n

  gt :
      n < m
      ---------
    → Trichotomy m n
    
  eq :
      m ≡ n
      ---------
    → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = eq refl
<-trichotomy zero (suc n) = lt z<s
<-trichotomy (suc m) zero = gt z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | lt m<n = lt (s<s m<n)
... | gt n<m = gt (s<s n<m)
... | eq refl = eq refl

{- Exercise +-mono-< (practice)

Show that addition is monotonic with respect to strict inequality. As with
inequality, some additional definitions may be required. -}

-- ∀ {m n p q : ℕ} → m < n → p < q → m + p < n + q

-- this is really an analogy to the +-mono-≤
+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)


{- Exercise ≤-iff-< (recommended)

Show that suc m ≤ n implies m < n, and conversely. -}

-- I got stuck with thinking what to do when I get suc m in LHS of the relationship, but in the end
-- I the only point was to reuse the same thing recursively
<-iff-≤ : ∀ (m n) → suc m ≤ n → m < n
<-iff-≤ zero (suc n) _ = z<s
<-iff-≤ (suc m) (suc n) sm≤sn = s<s (<-iff-≤ m n (inv-s≤s sm≤sn))

inv-s<s : ∀ {m n : ℕ} → suc m < suc n -> m < n
inv-s<s (s<s sm<sn) = sm<sn

≤-iff-< : ∀ (m n) → m < n → suc m ≤ n
≤-iff-< zero (suc n) _ = s≤s z≤n
≤-iff-< (suc m) (suc n) sm<sn = s≤s (≤-iff-< m n (inv-s<s sm<sn))


{- Exercise <-trans-revisited (practice)

Give an alternative proof that strict inequality is transitive, using the
relation between strict inequality and inequality and the fact that inequality
is transitive. -}

<-trans-≤ : ∀ (m n p : ℕ) → m < n → n < p → m < p
-- the problem here was that the <-iff-≤ needs suc m ≤ p
-- that can almost be done transitively:
-- suc m ≤ p can be prooved ≤-trans (suc m ≤ n) (n ≤ p)
-- suc m ≤ n can be prooved using ≤-iff-< m n mn - by definition it returns the (suc m)
-- but the same cannot be done for n ≤ p as we only get suc n ≤ p doing the same as for m n
-- that is why we need the helpers, to get from suc m ≤ n to m ≤ n
<-trans-≤  m n p mn np = <-iff-≤ m p (≤-trans (≤-iff-< m n mn) (≤-suc-l (≤-iff-< n p np))) where
  ≤-suc-l : ∀ {m n : ℕ} → suc m ≤ n → m ≤ n
  ≤-suc-l (s≤s mn) = ≤-suc-r mn where
    ≤-suc-r : ∀ {m n : ℕ} → m ≤ n → m ≤ suc n
    ≤-suc-r z≤n = z≤n
    ≤-suc-r (s≤s mn) = s≤s (≤-suc-r mn)


--
-- EVEN and ODD
--

-- recursive data type definition needs their type first
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc-e  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc-o   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- the suc and zero are now overloaded constructors
-- suc is either:
--
-- 1. suc : ℕ → ℕ
--
-- 2. suc : ∀ {n : ℕ}
--     → odd n
--       ------------
--     → even (suc n)
--
-- 3. suc : ∀ {n : ℕ}
--     → even n
--       -----------
--     → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

-- e+e≡e and o+e≡o are mutually recursive functions (need to be declard first)

e+e≡e zero     en  =  en
e+e≡e (suc-e om) en  =  suc-e (o+e≡o om en)

o+e≡o (suc-o em) en  =  suc-o (e+e≡e em en)

-- emn≡enm : ∀ {m n : ℕ} → odd m → odd n → even (m + n) ≡ even (n + m)
-- emn≡enm (suc {n} x) (suc {n₁} x₁) rewrite +-comm (suc n) (suc n₁) = refl

{- Exercise o+o≡e (stretch)

Show that the sum of two odd numbers is even.-}

-- From some reason I got quite stuck on this one,
-- as I was trying to use commutativity since the
-- o+e≡o x y was returning the odd (m + n) instead
-- of the other way around:

-- first try ended up quite horribly:

o+o≡e′ : ∀ {m n : ℕ} → odd m → odd n → even (n + m)
o+o≡e′ x (suc-o y) = suc-e (+-odd-comm x y (o+e≡o x y)) where
  +-odd-comm : ∀ {m n : ℕ} → odd m → even n → odd (m + n) → odd (n + m)
  +-odd-comm (suc-o m) zero _ = suc-o m
  +-odd-comm (suc-o {m} _) (suc-e {n} _) rewrite +-comm (suc m) (suc n) = λ z → z

-- second try, after renaming suc to suc-e and suc-o

o+o≡e″ : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e″ {m} x (suc-o {n} y)
  rewrite            -- even (m + suc n)
    +-comm m (suc n) -- even (suc (n + m))
  | +-comm n m       -- even (suc (m + n)) ≡ suc-e (odd (m + n))
  = suc-e (o+e≡o x y)

-- finally, a simple way is to double match on the first argument:

o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc-o zero) n = suc-e n
o+o≡e (suc-o (suc-e x)) n = suc-e (suc-o (o+o≡e x n))

-- I always try to explore a bit, by matching on all, one, ... but double
-- matching I used so far only twice, this included.


--
-- BINARY
--
open import 2-induction using (Bin; ⟨⟩; _O; _I; inc; from; to; +-suc)

eleven  = ⟨⟩ I O I I
eleven′ = ⟨⟩ O O I O I I
twelve  = ⟨⟩ I I O O
twelve′ = ⟨⟩ O O I I O O

{- Exercise:

Define a predicate

Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning it has no
leading zeros; the first representation of eleven above is canonical, and the
second is not. To define it, you will need an auxiliary predicate

One : Bin → Set

that holds only if the bistring has a leading one. A bitstring is canonical if
it has a leading one (representing a positive number) or if it consists of a
single zero (representing zero). -}

data One : Bin → Set where
  one-⟨⟩ : One (⟨⟩ I)
  one-O  : ∀ {b : Bin}
    → One b
      ---------
    → One (b O)
  one-I  : ∀ {b : Bin}
    → One b
      ---------
    → One (b I)

data  Can : Bin → Set where
  can-⟨⟩  : Can ⟨⟩
  can-one : ∀ {b : Bin} → One b → Can b

{- Exercise:

Show that increment preserves canonical bitstrings:

Can b
------------
Can (inc b) -}

-- tried a few things, but again matching twice on first param works
-- actually, it works using auto
inc-preserves-one : ∀ {b : Bin} -> Can b -> One (inc b)
inc-preserves-one can-⟨⟩ = one-⟨⟩
inc-preserves-one (can-one one-⟨⟩) = one-O one-⟨⟩
inc-preserves-one (can-one (one-O x)) = one-I x
inc-preserves-one (can-one (one-I x)) = one-O (inc-preserves-one (can-one x))

-- trying the same as with inc-preserves-one
inc-preserves-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-preserves-can can-⟨⟩ = can-one one-⟨⟩
inc-preserves-can (can-one one-⟨⟩) = can-one (one-O one-⟨⟩)
inc-preserves-can (can-one (one-O x)) = can-one (one-I x)
inc-preserves-can (can-one (one-I x)) = can-one (one-O (inc-preserves-one (can-one x)))

-- since, it is exactly the same as inc-preserves-one except the can-one prefix
-- it can be simplified into this:
inc-preserves-can′ : ∀ {b : Bin} → Can b → Can (inc b)
inc-preserves-can′ can = can-one (inc-preserves-one can)

{- Exercise: 

Show that converting a natural to a bitstring always yields a canonical bitstring:

----------
Can (to n) -}

to-yields-can : ∀ (n : ℕ) → Can (to n)
to-yields-can zero = can-⟨⟩
to-yields-can (suc n) = inc-preserves-can (to-yields-can n)

{- Exercise:

Show that converting a canonical bitstring to a natural and back is the identity:

Can b
---------------
to (from b) ≡ b

hint: you may need to prove that 1 is less or equal to the result of from b. -}

open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

to-2sn : ∀ (n : ℕ) → 0 ≤ n → to (suc n + suc n) ≡ (to (suc n)) O
to-2sn zero z≤n = refl
to-2sn (suc n) z≤n =
  begin -- goal:  (to (suc (suc n)) O) -- (inc (to (suc n)) O) --> (inc (int (to n)) O)
    to (suc (suc n) + suc (suc n))
  ≡⟨⟩
    to (suc (suc n + suc (suc n)))
  ≡⟨⟩
    to (suc (suc (n + suc (suc n))))
  ≡⟨ cong to (cong suc (cong suc (+-suc n (suc n)))) ⟩ -- getting to understand the power of rewrites
    to (suc (suc (suc n + suc n))) -- suc (n + suc n) --> suc(n + n)
  ≡⟨⟩
    inc (inc (to (suc n + suc n)))
  ≡⟨ cong inc (cong inc (to-2sn n z≤n)) ⟩
    inc (inc ((to (suc n)) O))
  ≡⟨⟩
    inc (inc (to n) I)
  ≡⟨⟩
    (inc (inc (to n))) O
  ≡⟨⟩
    (to (suc (suc n))) O
  ∎

-- ok, here is the version with rewrite
to-2sn′ : ∀ (n : ℕ) → to (suc n + suc n) ≡ (to (suc n)) O
to-2sn′ zero = refl
to-2sn′ (suc n) rewrite +-suc n (suc n) | to-2sn′ n = refl

to-2n : ∀ (n : ℕ) → 1 ≤ n → to (n + n) ≡ (to n) O
to-2n zero ()
to-2n (suc n) (s≤s 0≤n) = to-2sn n 0≤n

can-from-bO : ∀ {b : Bin} → One (b O) → Can b
can-from-bO (one-O one) = can-one one

can-from-bI : ∀ {b : Bin} → One (b I) → Can b
can-from-bI one-⟨⟩ = can-⟨⟩
can-from-bI (one-I one) = can-one one

1≤m+n : ∀ (m n : ℕ) → 1 ≤ m → 1 ≤ m + n
1≤m+n _ zero (s≤s 1≤m) = s≤s z≤n
1≤m+n _ (suc _) (s≤s 1≤m) = s≤s z≤n

1≤-from-bO : ∀ (b : Bin) → One (b O) → 1 ≤ from b
1≤-from-bO (b O) (one-O one) = 1≤m+n (from b) (from b) (1≤-from-bO b one)
1≤-from-bO (b I) (one-O one) = s≤s z≤n

1≤-from-bI : ∀ (b : Bin) → One (b I) → 1 ≤ from b
1≤-from-bI ⟨⟩ one-⟨⟩ = {!!}
1≤-from-bI (b O) (one-I one) = 1≤m+n (from b) (from b) (1≤-from-bO b one)
1≤-from-bI (b I) (one-I one) = s≤s z≤n

can-to-from : ∀ (b : Bin) → Can b → to (from b) ≡ b
can-to-from ⟨⟩ can-⟨⟩ = refl
can-to-from (b O) (can-one one) rewrite to-2n (from b) (1≤-from-bO b one) | can-to-from b (can-from-bO one) = refl
can-to-from (b I) (can-one one) rewrite to-2n (from b) (1≤-from-bI b one) | can-to-from b (can-from-bI one) = refl
