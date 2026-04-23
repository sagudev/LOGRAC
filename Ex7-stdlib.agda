{-# OPTIONS --prop #-}

---------------------------------------------------------------------------
-- Week 7 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Alex Simpson                                                --
-- Teaching Assistant: Luna Strah                                        --
--                                                                       --
-- Adapted from Danel Ahmans's exercises from 2022 available at:         --
-- https://github.com/danelahman/lograc-2022/blob/main/exercises/        --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
---------------------------------------------------------------------------

module Ex7-stdlib where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; _≢_)
open import Relation.Nullary using (¬_)

{-
   We also postulate the principle of function extensionality so
   that you can use it if and when needed in the exercises below.
-}

postulate
  fun-ext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x)
          → f ≡ g


-------------------------------
-------------------------------
-- SIMPLER EXERCISES [START] --
-------------------------------
-------------------------------

----------------
-- Exercise 0 --
----------------

{-
   Start by proving the following simple equational properties about natural numbers and addition.
   Hint: Use induction. You might find it useful to recall the congruence principle `cong` from
   lecture.
-}

+-identityʳ : (n : ℕ) → n + zero ≡ n
+-identityʳ zero = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-identityˡ : (n : ℕ) → zero + n ≡ n
+-identityˡ zero = refl
+-identityˡ (suc n) = refl

+-suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl


----------------
-- Exercise 1 --
----------------

{- Define the function `lookup` that looks up the value in a given vector at a given natural number
   index.

   As the index below can be an arbitrary natural number, then we have to define `lookup` as a
   partial function. We do this by giving `lookup` the `Maybe` return type, which has two
   constructors: one for the value if the function is defined, and one to mark that that the
   functions is not defined. Set-theoretically, `Maybe A` should be read as the disjoint union of
   sets `A` and `{ nothing }`. -}

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} {n : ℕ} → Vec A n → ℕ → Maybe A
lookup [] i = nothing
lookup (x ∷ xs) zero = just x
lookup (x ∷ xs) (suc i) = lookup xs i


----------------
-- Exercise 2 --
----------------

{-
   There are several ways of defining relations on types. For example, lets define the ≤ relation on
   natural numbers.
-}

module WithProp where
  data _≤_ : ℕ → ℕ → Prop where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

module WithSet where
  data _≤_ : ℕ → ℕ → Set where
    z≤n : {n : ℕ} → zero ≤ n
    s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

  infix 4 _≤_

module WithPropInd where
  open WithProp

  {-
    However trying to define a Type-elimination principle for `≤` with `Prop` fails. You can attempt
    to finish the definition below, but since you are unable to pattern-match on `p`.

    ERRATA: You can attempt to finish the definition below, but since you are unable to pattern-match on `p`,
    there is no way to extract a proof of `m ≤ n` from `p : suc m ≤ suc n`.
  -}
  module _ (P : (m n : ℕ) → Prop)
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind zero    n       p = pzn n
    ≤-ind (suc m) (suc n) (s≤s p) = pss m n (≤-ind m n p)
    -- ≤-ind (suc m) (suc n) p = pss m n (≤-ind m n p)


module WithSetInd where
  open WithSet

  module _ (P : (m n : ℕ) → Set)
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind m n z≤n = pzn n
    ≤-ind m n (s≤s p) = pss _ _ (≤-ind _ _ p)
    -- Here we must omit the arguments to `pss` and `≤-ind`, since they should be predecessors of
    -- `m` and n. Alternatively, we should pattern-match on `m` and `n` to extract their
    -- predecessors (we already know they are successors).


module WithPropButWithSetEliminationAsWell where

  data ⊥ᵖ : Prop where

  record ⊤ᵖ : Prop where
    constructor tt

  _≤_ : ℕ → ℕ → Prop
  zero  ≤ n     = ⊤ᵖ
  suc m ≤ zero  = ⊥ᵖ
  suc m ≤ suc n = m ≤ n

  infix 4 _≤_

module WithPropButWithSetEliminationAsWellInd where
  open WithPropButWithSetEliminationAsWell

  module _ {P : (m n : ℕ) → Set}
    (pzn : (n : ℕ) → P zero n)
    (pss : (m n : ℕ) → P m n → P (suc m) (suc n)) where

    ≤-ind : (m n : ℕ) → m ≤ n → P m n
    ≤-ind zero n p = pzn n
    ≤-ind (suc m) (suc n) p = pss m n (≤-ind m n p)

{-
   At various times we will be comparing the two definitions, so we import both. We shall try to
   work with the definition using `Prop` defined as a function, however that might change in the
   future. Feel free to comment out the modules `WithProp` and `WithPropInd` above, if you feel they
   pollute your workspace.
-}

open WithPropButWithSetEliminationAsWell
open WithSet using () renaming (_≤_ to _≤ˢ_; z≤n to z≤ˢn; s≤s to s≤ˢs)

≤-to-≤ˢ : (m n : ℕ) → m ≤ n → m ≤ˢ n
≤-to-≤ˢ zero n p = z≤ˢn
≤-to-≤ˢ (suc m) (suc n) p = s≤ˢs (≤-to-≤ˢ m n p)

≤ˢ-to-≤ : (m n : ℕ) → m ≤ˢ n → m ≤ n
≤ˢ-to-≤ zero n p = tt
≤ˢ-to-≤ (suc m) (suc n) (s≤ˢs p) = ≤ˢ-to-≤ m n p


----------------
-- Exercise 3 --
----------------

{-
   Show that `≤` gives a partial order on ℕ.
-}

reflexive : (n : ℕ) → n ≤ n
reflexive zero = tt
reflexive (suc n) = reflexive n

transitive : (m n k : ℕ) → m ≤ n → n ≤ k → m ≤ k
transitive zero n k r1 r2 = tt
transitive (suc m) (suc n) (suc k) r1 r2 = transitive m n k r1 r2


anti-symmetric : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
anti-symmetric zero zero r1 r2 = refl
anti-symmetric (suc m) (suc n) r1 r2 = cong suc (anti-symmetric m n r1 r2)


----------------
-- Exercise 4 --
----------------

{-
   Show that `≤ˢ` is also anti-symmetric.
-}

anti-symmetricˢ : (m n : ℕ) → m ≤ˢ n → n ≤ˢ m → m ≡ n
anti-symmetricˢ m n r1 r2 = anti-symmetric m n (≤ˢ-to-≤ m n r1) (≤ˢ-to-≤ n m r2)


----------------
-- Exercise 5 --
----------------

{-
   Consider a strict comparison relation on the naturals.
-}

_<_ : ℕ → ℕ → Prop
n < m = suc n ≤ m

_>_ : ℕ → ℕ → Prop
n > m = m < n

infix 4 _<_
infix 4 _>_


{-
   This allows us to state (and prove) a correctness theorem for `lookup` from earlier. For
   simplicity we shall only consider vectors over the unit type `⊤`.
-}


open import Data.Unit

lookup-totalᵀ : {n : ℕ}
              → (xs : Vec ⊤ n)
              → (i : ℕ)
              → i < n
              → lookup xs i ≡ just tt
lookup-totalᵀ (x ∷ xs) zero p = refl
lookup-totalᵀ (x ∷ xs) (suc i) p = lookup-totalᵀ xs i p


----------------
-- Exercise 6 --
----------------

{-
   The `lookup-totalᵀ` lemma above is commonly called an "extrinsic" proof because we prove the
   correctness of `lookup` after the fact, externally to its (simply typed, regarding the index `i`)
   definition.

   In contrast, we could instead make use of the expressiveness of dependent types and define an
   alternative `safe-lookup` function that is total and guaranteed to always return a value of type
   `A`. In this case one will have to prove that the index is in the range in order to be able to
   call the `safe-lookup` function below.

   We do this by restricting the index argument of the function to be from the finite set of natural
   numbers `{ 0 , 1 , ... , n - 1 }` already in the type signature of the lookup function. For this
   we will use the dependent type `Fin` defined below. As this "correctness of the index argument"
   specification is now imposed in the types at definition time, this style of proof is commonly
   called "intrinsic".

   Intuitively, `Fin n` is the finite set `{ 0 , 1 , ... , n - 1 }`.
-}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

safe-lookup : {A : Set} {n : ℕ} → Vec A n → Fin n → A
safe-lookup (x ∷ xs) zero = x
safe-lookup (x ∷ xs) (suc i) = safe-lookup xs i

{-
   Think about how to define a safe lookup function for lists.

A: you can't
-}


----------------
-- Exercise 7 --
----------------

{-
   Prove that the two lookup functions compute the same value if the given index is in an
   appropriate range.

   In order to pass the given natural number `i` as an argument to the `safe-lookup` function, you
   will have to convert it to an element of `Fin` with the `nat-to-fin` function. As a challenge,
   the type of `nat-to-fin` is left for you to complete (notice the hole in the type). Hint: You
   should be able to reverse-engineer it from its use in the type of `lookup-correct` below. If you
   fill the hole with the correct type, the yellow highlighting below will disappear. -}

nat-to-fin : {n : ℕ} → (nn : ℕ) → (p : nn < n) → Fin n
nat-to-fin {suc n} zero p = zero
nat-to-fin {suc n} (suc nn) p = suc (nat-to-fin {n} nn p)

lookup-correct : {A : Set} {n : ℕ}
               → (xs : Vec A n)
               → (i : ℕ)
               → (p : i < n)
               → lookup xs i ≡ just (safe-lookup xs (nat-to-fin i p))
lookup-correct (x ∷ x₁) zero p = refl
lookup-correct (x ∷ x₁) (suc i) p = lookup-correct x₁ i p


----------------
-- Exercise 8 --
----------------

{-
   Recall the conversion maps between vectors and lists.
-}

to-list : {A : Set} {n : ℕ} → Vec A n → List A
to-list [] = []
to-list (x ∷ xs) = x ∷ to-list xs

to-vec : {A : Set} (xs : List A) → Vec A (length xs)
to-vec [] = []
to-vec (x ∷ xs) = x ∷ to-vec xs

{-
   Prove that the `to-list` function produces a list with the same length as the given vector.
-}

to-list-length : {A : Set} {n : ℕ}
                → (xs : Vec A n)
                → n ≡ length (to-list xs)
to-list-length [] = refl
to-list-length {_} {suc n} (x ∷ xs) = cong suc (to-list-length xs)


-------------------------------------
-------------------------------------
-- MORE INVOLVED EXERCISES [START] --
-------------------------------------
-------------------------------------

open import Function using (id; _∘_)

-----------------
-- Exercise 9 --
-----------------

{-
   Prove that `to-list` is the left inverse of `to-vec`. Observe that you have to prove equality
   between functions.
-}

list-vec-list : {A : Set}
              → (to-list ∘ to-vec) ≡ id {A = List A}
list-vec-list = {!!}


-----------------
-- Exercise 10 --
-----------------

{-
   Show equality on the natural numbers is decidable.
-}

data _</≡/>_ (m n : ℕ) : Set where
  m<n : m < n → m </≡/> n
  m≡n : m ≡ n → m </≡/> n
  m>n : m > n → m </≡/> n

{-
   Define a function `test-</≡/>` that, given two natural numbers, returns the proof of either
   `n < m`, `n ≡ m`, or `n > m` depending on the relationship between the given two numbers.

   In its essence, the function `test-</≡/>` shows that the natural ordering relation on natural
   numbers is total and decidable---we can compute which of the three situations actually holds. See
   PLFA (https://plfa.inf.ed.ac.uk/Decidable/) for more details.
-}

test-</≡/> : (m n : ℕ) → m </≡/> n
test-</≡/> zero zero = m≡n refl
test-</≡/> zero (suc n) = m<n tt
test-</≡/> (suc m) zero = m>n tt
test-</≡/> (suc m) (suc n) with (test-</≡/> m n)
... | m<n p = m<n p
... | m≡n p = m≡n (cong suc p)
... | m>n p = m>n p


-----------------
-- Exercise 11 --
-----------------

{-
   Below is the inductive type `Tree A` of node-labelled binary trees holding data of type `A` in
   their nodes. Such a tree is either an `empty` tree (holding no data); or a root node built from a
   left subtree `t`, data `n`, and a right subtree `u`, written `node t n u`.

   For example, the binary tree

           42
           /\
          /  \
         22  52
          \
           \
           32

   would be represented in Agda as the expression

     `node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)`

   of type `Tree ℕ`.
-}

data Tree (A : Set) : Set where
  empty : Tree A
  node  : Tree A → A → Tree A → Tree A

{-
   For trees holding natural numbers, define a function that inserts a given natural number into a
   tree following the insertion strategy for binary search trees
   (https://en.wikipedia.org/wiki/Binary_search_tree).

   Namely, when inserting a number `n` into an `empty` tree, the function should create a new
   trivial tree containing just `n`; and when recursively inserting a number `n` into a tree of the
   form `node t m u`, the function should behave as one of the following three cases: - if n = m,
   then the function just returns the given tree, doing nothing; - if n < m, then the function
   recursively tries to add `n` into `t`; or - if n > m, then the function recursively tries to add
   `n` into `u`.

   Hint: When testing which of the three situations holds for a `node t m u` case, you might find it
   helpful to use Agda's `with` abstraction
   (https://agda.readthedocs.io/en/v2.6.2.1/language/with-abstraction.html) to do perform
   pattern-matching without having to define auxiliary functions.
-}

insert : Tree ℕ → ℕ → Tree ℕ
insert = {!!}

{-
   As a sanity check, prove that inserting 12, 27, and 52 into the above example tree correctly
   returns the expected trees.

ERRATA: You can skip the sanity check proofs. If you have time you can come back to them.
They were intended to be solved using equational reasoning, which I have not introduced.
You can look at more details here or here.
Import `open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)` from the standard library to use it,
or copy the definition from PLFA.
-}

insert-12 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 12
            ≡
            node (node (node empty 12 empty) 22 (node empty 32 empty)) 42 (node empty 52 empty)
insert-12 = {!!}

insert-27 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 27
            ≡
            node (node empty 22 (node (node empty 27 empty) 32 empty)) 42 (node empty 52 empty)
insert-27 = {!!}

insert-52 : insert (node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)) 52
            ≡
            node (node empty 22 (node empty 32 empty)) 42 (node empty 52 empty)
insert-52 = {!!}


-----------------
-- Exercise 12 --
-----------------

{-
   Define an inductive relation `∈` that specifies that a given natural number exists in the given
   tree.

   Hint: This relation should specify a path in a given tree from its root to the desired natural
   number whose existence we are specifying.
-}

data _∈_ (n : ℕ) : Tree ℕ → Set where
  {- EXERCISE: the constructors for the `∈` relation go here -}


{-
   Prove that the tree returned by the `insert` function indeed contains the inserted natural
   number.

   Hint: If you used Agda's `with` abstraction for pattern-matching in the definition of `insert`,
   you will need to perform similar amount of pattern-matching also in this proof to make the type
   of the hole compute. You can tell when this is needed because the type of the hole will involve
   an expression of the form `f v | g w`, meaning that in order for `f v` to be computed and
   normalised further, you need to first pattern-match on the value of `g v` (using `with`).

   If you haven't spotted this already, then it is part of a general pattern---proofs often follow
   the same structure as the definitions.
-}

insert-∈ : (t : Tree ℕ) → (n : ℕ) → n ∈ (insert t n)
insert-∈ t n = {!!}


-------------------------------------
-------------------------------------
-- MOST INVOLVED EXERCISES [START] --
-------------------------------------
-------------------------------------

-----------------
-- Exercise 13 --
-----------------

{-
   While above you were asked to define the `insert` function following the insertion strategy for
   binary search trees, then concretely the function is still working on arbitrary binary trees.
   Here we will define an inductive predicate to classify binary trees that are indeed binary search
   trees and prove that the `insert` function preserves this predicate.
-}

{-
   Before we define the binary search tree predicate, we extend the type of natural numbers with
   bottom and top elements, written `-∞` and `+∞` (for symmetry and their analogy with negative and
   positive infinities; also, `⊥` and `⊤` are already used in Agda for the empty and unit type). We
   then also extend the order `<` to take these new bottom and top elements into account.
-}

data ℕ∞ : Set where
  -∞  :     ℕ∞
  [_] : ℕ → ℕ∞
  +∞  :     ℕ∞

_<∞_ : ℕ∞ → ℕ∞ → Prop
-∞ <∞ n = ⊤ᵖ
[ m ] <∞ -∞ = ⊥ᵖ
[ m ] <∞ [ n ] = m < n
[ m ] <∞ +∞ = ⊤ᵖ
+∞ <∞ n = ⊥ᵖ

{-
   Using this extended definition of natural numbers, we next define an inductive predicate `IsBST`
   on binary trees that specifies when a given binary tree holding natural numbers is in fact a
   binary search tree (https://en.wikipedia.org/wiki/Binary_search_tree).

   Note that, concretely, the `IsBST` predicate consists of two definitions:
   - the `IsBST` predicate, which is the "top-level" predicate specifying that a given binary tree
     is in a binary search tree format; and
   - the recursively defined relation `IsBST-rec`, which does most of the work in imposing the
     binary search tree invariant on the given tree.

   The `IsBST-rec` relation carries two additional `ℕ∞`-arguments that specify the range of values a
   given binary search tree is allowed to hold, in particular, which values the left and right
   subtrees of a `node t n u` tree node are allowed to store. Further, note that the `empty` case
   holds a proof that `lower` is indeed less than `upper`.
-}

data IsBST-rec (lower upper : ℕ∞) : Tree ℕ → Set where
  empty-bst : {p : lower <∞ upper} → IsBST-rec lower upper empty
  node-bst  : {t u : Tree ℕ} {n : ℕ}
            → IsBST-rec lower [ n ] t
            → IsBST-rec [ n ] upper u
            → IsBST-rec lower upper (node t n u)

data IsBST : Tree ℕ → Set where
  empty-bst : IsBST empty
  node-bst  : {t u : Tree ℕ} {n : ℕ}
            → IsBST-rec -∞ [ n ] t
            → IsBST-rec [ n ] +∞ u
            → IsBST (node t n u)

{-
   Prove that having the `{p : lower <∞ upper}` proof witness in the `empty` cases of the
   `IsBST-rec` relation indeed forces the `<∞` relation to hold for the bound indices of `IsBST-rec`
   in general.

   Hint: You might find it helpful to prove the transitivity of `<∞`.
-}

isbst-rec-<∞ : {lower upper : ℕ∞} {t : Tree ℕ}
             → IsBST-rec lower upper t
             → lower <∞ upper
isbst-rec-<∞ = {!!}

bst : IsBST (node (node empty 2 (node empty 3 empty)) 5 (node empty 6 empty))
bst = node-bst
        (node-bst
           empty-bst
           (node-bst
              empty-bst
              empty-bst))
        (node-bst
           empty-bst
           empty-bst)


-----------------
-- Exercise 14 --
-----------------

{-
   We could define all the above with `Prop`, however this turns out to behave worse. You can try
   it out by defining `isbst-recᵖ-<∞` for the version below.

-}

record Σᵖ (p : Prop) (q : p → Prop) : Prop where
  constructor _,_
  field
    fst : p
    snd : q fst

infixl 6 _∧_
_∧_ : Prop → Prop → Prop
p ∧ q = Σᵖ p λ _ → q

IsBST-recᵖ : (lower upper : ℕ∞) → Tree ℕ → Prop
IsBST-recᵖ lower upper empty = lower <∞ upper
IsBST-recᵖ lower upper (node t n u) = IsBST-recᵖ lower [ n ] t ∧ IsBST-recᵖ [ n ] upper u

IsBSTᵖ : Tree ℕ → Prop
IsBSTᵖ empty = ⊤ᵖ
IsBSTᵖ (node t n u) = IsBST-recᵖ -∞ [ n ] t ∧ IsBST-recᵖ [ n ] +∞ u

isbst-recᵖ-<∞ : {lower upper : ℕ∞} {t : Tree ℕ}
             → IsBST-recᵖ lower upper t
             → lower <∞ upper
isbst-recᵖ-<∞ = {!!}

{-
   In fact, defining `<∞` as we did above also makes the definition of transitivity worse. Try
   defining it as a datatype in `Set` and compare the proofs of transitivity.
-}



-----------------
-- Exercise 15 --
-----------------

{-
   Prove that being a binary search tree is invariant under `insert`.

   Hint: As the `IsBST` predicate is defined in two steps, then you might find it useful to prove an
   auxiliary lemma about `insert` preserving also the recursively defined `IsBST-rec` relation.
-}

insert-bst : (t : Tree ℕ) → (n : ℕ) → IsBST t → IsBST (insert t n)
insert-bst = {!!}

-----------------
-- Exercise 16 --
-----------------

{-
   Prove that `list-vec` is the left inverse of `vec-list`. Observe that you have to prove equality
   between functions.

   Note that if we simply wrote `id` as the right-hand side of the equational property below we
   would get a typing error about a mismatch in the natural number indices. Find a way to fix the
   type of a given vector to use it in the right-hand side of the equation.

   Hint 1: For a slightly unsatisfactory solution, think how you could convert a given vector to
   another of a given type using recursion.

   Hint 2: For a more complete solution, recall from the exercises how one change the type of a
   given value (e.g., a vector) using a previously proved equality proof, and then combine this with
   one of the equational lemmas we proved above.

   WARNING: The hint 2 solution of this exercise is probably the most complex on this exercise
   sheet, as it will require some careful thought when generalising the concrete statement you are
   trying to prove, relating element-wise equality of vectors to the `≡` relation on vectors, etc.
   So we suggest you leave this one for the very last. -}

vec-list-vec : {A : Set} {n : ℕ}
             → to-vec ∘ to-list ≡ {!!}
vec-list-vec = {!!}
