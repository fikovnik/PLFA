module 2-induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

{- Exercise: give an example of an operator that has an identity and is
   associative but is not commutative. -}

{- For example: string concatenation, cons -}

{- Associativity: (m + n) + p ≡ m + (n + p)

Proof by induction:

------
P zero

P m
---------
P (suc m)

In this case:

P m is (m + n) + p ≡ m + (n + p)

-------------------------------
(zero + n) + p ≡ zero + (n + p)

(m + n) + p ≡ m + (n + p)
---------------------------------
(suc m + n) + p ≡ suc m + (n + p)  -}

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    {- I start with left-hand side of what I'm trying to proof, i.e. (m + n) + p ≡ ... -}
    (suc m + n) + p
  ≡⟨⟩
    {- Next, I move the suc to the left. This is the inductive case of _+_ -}
    suc (m + n) + p
  ≡⟨⟩
    {- Since _+_ is left associate, the above is actually the following -}
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    {- The +-assoc provides an evidence for (m + n) + p ≡ m + (n + p).
       The call to cong will turn this into: suc ((m + n) + p) ≡ suc (m + (n + p)).
       This allows me to substitute the LHS for RHS. -}
    suc (m + (n + p))
  ≡⟨⟩
    {- This is the same as the line above. -}
    suc m + (n + p)
  ∎

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = refl

{- induction as reduction -}
+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎

{- Commutativity: m + n ≡ n + m -}

{- The base case of the definition of addition states that zero is a left-identity:

  zero + n ≡ n -}

{- The following lemma states that zero is also a right-identity:

  m + zero ≡ m -}

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m

-- goal is to proove: zero + zero ≡ zero
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎

-- goal is to proove: (suc m) + zero = suc m
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩ -- this applies suc to both sides of the +-identityʳ
    suc m
  ∎

{- The inductive case of the definition of addition pushes suc on the first
argument to the outside:

  suc m + n ≡ suc (m + n) -}

{- The second lemma does the same for suc on the second argument:

  m + suc n ≡ suc (m + n) -}

+-suc : ∀ (m n) → m + suc n ≡ suc (m + n)

-- zero + suc n ≡ suc (zero + n)
+-suc zero n = refl

-- suc m + suc n ≡ suc (suc m + n)
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

_ : 1 + suc 3 ≡ suc (1 + 3)
_ = refl

_ : 1 + suc 3 ≡ suc 1 + 3
_ = refl


+-comm : ∀ (m n : ℕ) → m + n ≡ n + m

-- From some reason (a good though) "we" decided to case split on n. Actually,
-- the reason is that it will be easier, but it is also the reason why we need
-- the +-suc lemma, becase now, the zero and (suc n) will be on the right part
-- of the equation.
--
-- First, I need to show that m + zero ≡ zero + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    zero + m
  ∎

{- The inductive case of the proof.
   Now n = (suc n).
   I need to show that m + suc n ≡ suc n + m
   I know that m + suc n ≡ suc (m + n) thanks to the +-suc lemma
   I know that suc (m + n) ≡ suc m + n thanks to the inductive case of _+_ -}
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    {- Using the lemma defined above - the inductive case of +-suc, I can push
    the suc in front -}
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    {- +-comm provides evidence for m + n ≡ n + m
       The congurence make it suc (m + n) ≡ suc (n + m)
       I need to show that m + (suc n) ≡ (suc n) + m, which is the same as
                           m + (suc n) ≡ suc (n + m) becasue of the inductive case of _+_ -}
    suc (n + m)
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    {- The +-assoc provides an evidence for (m + n) + p ≡ m + (n + p) for ∀ m n p.
       Substituting p for (p + q) I can rewrite the above to: -}
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    {- So far I was using the evidences x ≡ y to rewrite x to y.
       It can be used the other way around via the call to ≡ sym -}
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

{- Exercise: Write out what is known about associativity of addition on each of
   the first four days using a finite story of creation, as earlier. -}

_ : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
_ = λ n p → refl

_ : ∀ (n p) → (1 + n) + p ≡ 1 + (n + p)
_ = λ n p → refl


-- Commutativity using rewrite


+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


-- Building proofs interactivelly

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
-- Goal: suc (m + n + p) ≡ suc (m + (n + p))
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

{- Exercise: Show

m + (n + p) ≡ n + (m + p)

for all naturals m, n, and p. No induction is needed, just apply the previous
results which show addition is associative and commutative. -}

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm′ m (n + p) | +-assoc′ n p m | +-comm′ m p = refl

{- Exercise *-distrib-+ (recommended)

Show multiplication distributes over addition, that is,

(m + n) * p ≡ m * p + n * p

for all naturals m, n, and p. -}

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc′ p (m * p) (n * p) = refl

-- *-distrib-+ (suc m) n p = ? has goal:
-- p + (m + n) * p ≡ p + m * p + n * p
--
-- *-distrib-+ (suc m) n p rewrite *-distrib-+ m n p = ? has goal:
-- p + (m * p + n * p) ≡ p + m * p + n * p
--
-- *-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc′ p (m * p) (n * p) = ? has goal:
-- p + (m * p + n * p) ≡ p + (m * p + n * p)

*-distrib-+′ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+′ zero n p = refl
*-distrib-+′ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+′ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc′ p (m * p) (n * p)) ⟩
    p + m * p + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

{- Exercise *-assoc (recommended)

Show multiplication is associative, that is,

(m * n) * p ≡ m * (n * p)

for all naturals m, n, and p. -}

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-assoc m n p | *-distrib-+ n (m * n) p | *-assoc m n p = refl

{- Exercise *-comm (practice)

Show multiplication is commutative, that is,

m * n ≡ n * m

for all naturals m and n. -}

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
  (suc m) * (suc n)
  ≡⟨⟩
  (suc n) + (m * suc n)
  ≡⟨⟩
  suc (n + m * suc n)
  ≡⟨ cong (suc n +_) (*-suc m n) ⟩
  suc n + (m + m * n)
  ≡⟨⟩
  suc (n + (m + m * n))
  ≡⟨ cong (suc n +_) (+-comm m (m * n)) ⟩
  suc (n + (m * n + m))
  ≡⟨ cong suc (sym (+-assoc n (m * n) m)) ⟩
  suc (n + m * n + m)
  ≡⟨ cong suc (+-comm (n + m * n) m) ⟩
  suc (m + (n + m * n))
  ≡⟨⟩
  suc (m + suc m * n)
  ≡⟨⟩
  (suc m) + (suc m) * n
  ∎

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-suc m 0 | *-zero m = refl
*-comm m (suc n) rewrite *-suc m n | *-comm m n = refl

{- Exercise 0∸n≡0 (practice)

Show

zero ∸ n ≡ zero

for all naturals n. Did your proof require induction? -}

0∸n≡0 : ∀ n → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

{- Exercise ∸-+-assoc (practice)

Show that monus associates with addition, that is,

m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals m, n, and p. -}

{- I first did case split on n which relf out the first case. Then I tried case
split on m. I think it would be easier with the ∸ definition from first chapter,
rather than the definiton from the stdlib. -}

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite 0∸n≡0 p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

{- Exercise +*^ (stretch)

Show the following three laws

 m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
 (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
 (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)

for all m, n, and p. -}

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identity′ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

{- After applying the ^-distribʳ-* it looked like it is almost done, but then it
   took a while. The way forward was to actually start from the bottom, write
   all the steps, insert ≡⟨ ? ⟩ and then solve the holes with cong. -}
^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) * ((m * n) ^ p)
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
  ≡⟨ sym (*-assoc (m * n) (m ^ p) (n ^ p)) ⟩
    ((m * n) * (m ^ p)) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (*-assoc m n (m ^ p)) ⟩
    (m * (n * (m ^ p))) * (n ^ p)
  ≡⟨ cong (_* (n ^ p)) (cong (m *_) (*-comm n (m ^ p))) ⟩
    (m * ((m ^ p) * n)) * (n ^ p)
  ≡⟨ *-assoc m ((m ^ p) * n) (n ^ p) ⟩
    m * (((m ^ p) * n) * (n ^ p))
  ≡⟨ cong (m *_) (*-assoc (m ^ p) n (n ^ p)) ⟩
    m * ((m ^ p) * (n * (n ^ p)))
  ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ≡⟨⟩
  (m ^ (suc p)) * (n ^ (suc p))
  ∎

{- This is the same, but written using rewrites. I did that this step by step,
   commenting lines from the original proof. The thing is that without the the
   comment on the right side, it is unreadble for me at least. So whle it is
   easier to write (getting rid of the congurences), after it is constructed, I
   cannot read it back :-). -}

^-distribʳ-*′ : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-*′ m n zero = refl
^-distribʳ-*′ m n (suc p) rewrite          -- (m * n) * ((m * n) ^ p)
  ^-distribʳ-*′ m n p                      -- (m * n) * ((m ^ p) * (n ^ p))
  | sym (*-assoc (m * n) (m ^ p) (n ^ p))  -- ((m * n) * (m ^ p)) * (n ^ p)
  | *-assoc m n (m ^ p)                    -- (m * (n * (m ^ p))) * (n ^ p)
  | *-comm n (m ^ p)                       -- (m * ((m ^ p) * n)) * (n ^ p)
  | *-assoc m ((m ^ p) * n) (n ^ p)        -- m * (((m ^ p) * n) * (n ^ p))
  | *-assoc (m ^ p) n (n ^ p)              -- m * ((m ^ p) * (n * (n ^ p)))
  | sym (*-assoc m (m ^ p) (n * (n ^ p)))  -- m * (m ^ p) * (n * (n ^ p))
  = refl

n*0≡0 : ∀ n → n * zero ≡ zero
n*0≡0 zero = refl
n*0≡0 (suc n) rewrite n*0≡0 n = refl


^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite n*0≡0 n = refl
^-*-assoc m n (suc p) rewrite  -- (m ^ n) * ((m ^ n) ^ p) ≡ (m ^ (n * suc p))
  *-comm n (suc p)             -- (m ^ n) * ((m ^ n) ^ p) ≡ (m ^ (n + p * n))
  | ^-distribˡ-+-* m n (p * n) -- (m ^ n) * ((m ^ n) ^ p) ≡ (m ^ n) * (m ^ (p * n))
  | *-comm p n                 -- (m ^ n) * ((m ^ n) ^ p) ≡ (m ^ n) * (m ^ (n * p))
  | sym (^-*-assoc m n p)      -- (m ^ n) * ((m ^ n) ^ p) ≡ (m ^ n) * ((m ^ n) ^ p)
   = refl

{- Exercise Bin-laws (stretch)

Recall that Exercise Bin defines a datatype Bin of bitstrings representing natural numbers, and asks you to define functions

inc   : Bin → Bin
to    : ℕ → Bin
from  : Bin → ℕ

Consider the following laws, where n ranges over naturals and b over bitstrings:

from (inc b) ≡ suc (from b)
to (from b) ≡ b
from (to n) ≡ n

For each law: if it holds, prove; if not, give a counterexample. -}

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

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = 2 * from m
from (m I) = 1 + 2 * from m

from-inc-b : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc-b ⟨⟩ = refl
from-inc-b (b O) = refl
from-inc-b (b I) rewrite
  +-identity′ (from b)
  | +-identity′ (from (inc b))
  | from-inc-b b
  | +-suc (suc (from b)) (from b) = refl

-- to-from-b : ∀ (b : Bin) → to (from b) ≢ b
-- counter example to (from ⟨⟩) ≡ ⟨⟩ O ≢ ⟨⟩
-- case splittinfg on b will make this the first case

from-to-n : ∀ (n : ℕ) → from (to n) ≡ n
from-to-n zero = refl
from-to-n (suc n) rewrite from-inc-b (to n) | from-to-n n = refl
