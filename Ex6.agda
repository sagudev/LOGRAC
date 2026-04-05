---------------------------------------------------------------------------
-- Week 6 exercises for the Logika v računalništvu course at UL FMF      --
-- Lecturer: Alex Simpson                                                --
-- Teaching Assistant: Luna Strah                                        --
--                                                                       --
-- Adapted from Danel Ahmans's exercises from 2022 available at:         --
-- https://github.com/danelahman/lograc-2022/blob/main/exercises/        --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
---------------------------------------------------------------------------
module Ex6 where

----------------
-- Exercise 0 --
----------------

{-
   Begin by loading this Agda file in the editor of your choice (VS Code or Emacs, see README.md)
   using the `C-c C-l` command (to be read as pressing the `Ctrl` and `c` keys simultaneously,
   followed by pressing `Ctrl` and `l` keys simultaneously).

   If you have Agda set up correctly, then this should start the typechecking process on the given
   file. If the file loading and typechecking succeeds, the syntax should get colour-highlighted,
   and an additional buffer should appear and list the open goals (holes in Agda terminology) that
   need to be filled in this file:

   ?0 : ℕ
   ?1 : ℕ
   ...
   ?16 : f x ≡ f y
   ?17 : B y
   ?18 : tr p (f x) ≡ f y
-}


----------------
-- Exercise 1 --
----------------

{-
   Recall the type of natural numbers from the lecture.
-}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-} -- omogoči delovanje naravnih literalov
-- lol
{-
   Define a function that increments the given number by one.

   You can pattern-match on the function arguments by writing the name of the corresponding argument
   in the hole in the right-hand side of the definition, and then running the `C-c C-c` command with
   the cursor placed in the given hole.

   You can fill and complete a hole with what you have written in it by putting the cursor in the
   hole and then running the `C-c C-space` command. If you attempted to fill a hole with a term of
   incorrect type (say using something other than a natural number), Agda will report a typechecking
   error.
-}

incr : ℕ → ℕ
incr n = suc n

{-
   Define a function that decrements a number by one. Give the definition using pattern-matching.
   Decrementing the number zero should return zero.
-}

decr : ℕ → ℕ
decr zero = zero
decr (suc n) = n

{-
   Define a function that triples the value of a given number. Your definition should use both
   pattern-matching and recursion.
-}

triple : ℕ → ℕ
triple zero = zero
triple (suc n) = (suc (suc (suc (triple n))))


----------------
-- Exercise 2 --
----------------

{-
   Recall the defintion of `+` from the lecture and/or exercise classes.
-}

_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

infixl 6  _+_

{-
   Define multiplication and exponentiation (`m^n`) using pattern-matching, recursion, and the
   operations on natural numbers defined above.
-}

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)
{-
   After finishing the task above uncomment the line below. If you made a mistake in the definition,
   Agda should give you an error once you reload.
-}
{-# BUILTIN NATTIMES _*_ #-}

infixl 7  _*_

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ suc n = m * (m ^ n)

infixl 8  _^_


----------------
-- Exercise 3 --
----------------

{-
   Another common inductive data structure you will often see in functional programming and in Agda
   is that of lists (holding elements of some type `A`), given by constructors for the empty list
   and for concatenating a new element to a given list.

   For example, the sequence of numbers 0, 1, 2 would be expressed in Agda as a list as the
   expression `0 ∷ 1 ∷ 2 ∷ []` of type `List ℕ`.
-}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}
{-
   Define the `length` function that computes the length of a given list.
-}

length : {A : Set} → List A → ℕ
length [] = 0
length (x ∷ xs) = 1 + (length xs)


----------------
-- Exercise 4 --
----------------

{-
   Define the `map` function on lists that applies a given function of type `A → B` to every element
   of a given list of type `List A` and returns a list of type `List B`. In other words, the
   application `map f (0 ∷ 1 ∷ 2 ∷ [])` should return `f 0 ∷ f 1 ∷ f 2 ∷ []`.
-}

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = (f x) ∷ (map f xs)


----------------
-- Exercise 5 --
----------------

{-
   We can similarly define the type of vectors.
-}

data Vec (A : Set) : ℕ → Set where
  []ᵛ  : Vec A 0
  _∷ᵛ_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _∷ᵛ_

{-
   Define the `length` function that computes the length of a given vector.
-}

lengthᵛ : {A : Set} {n : ℕ} → Vec A n → ℕ
lengthᵛ {n = n} xs = n


----------------
-- Exercise 6 --
----------------

{-
   Define the `map` function on vectors.
-}

mapᵛ : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
mapᵛ f []ᵛ = []ᵛ
mapᵛ f (x ∷ᵛ xs) = (f x) ∷ᵛ (mapᵛ f xs)


----------------
-- Exercise 7 --
----------------

{-
   Define the maps between vectors and lists.
-}

to-list : {A : Set} {n : ℕ} → Vec A n → List A
to-list []ᵛ = []
to-list (x ∷ᵛ xs) = x ∷ to-list xs

to-vec : {A : Set} (xs : List A) → Vec A (length xs)
to-vec [] = []ᵛ
to-vec (x ∷ xs) = x ∷ᵛ to-vec xs


----------------
-- Exercise 8 --
----------------


{-
   Define concatenation of lists and vectors.
-}

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ( xs ++ ys )

_++ᵛ_ : {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[]ᵛ ++ᵛ ys = ys
(x ∷ᵛ xs) ++ᵛ ys = x ∷ᵛ ( xs ++ᵛ ys )


----------------
-- Exercise 9 --
----------------


{-
   The type of propositional equality is defined as follows.
-}

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}

{-
   Show `≡` is an equivalence relation.
-}

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
-- goal:
-- x = x
symm refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- x = x
trans refl refl = refl

-- tko je to v zvesku
-- id : {A : Set} → A → A
-- id x = x
-- trans refl q = id q

{-
   Furthermore, transitivity is associative.
-}

assoc : {A : Set} {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
      → trans (trans p q) r ≡ trans p (trans q r)
-- trans (trans refl refl) refl ≡ trans refl (trans refl refl)
--              trans refl refl ≡ trans refl refl      by       trans refl refl = refl
-- C-c C-. will show normalized goals!
assoc refl refl refl = refl


-----------------
-- Exercise 10 --
-----------------


{-
   There are some more useful properties of propositional equalities. If two elements of a type are
   propositionally equal we can essentially replace one with the other.

   This will help us define more complicated things later.
-}

ap : {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
-- f x ≡ f x
ap f refl = refl

tr : {A : Set} {B : A → Set} {x y : A} → x ≡ y → B x → B y
-- B x
tr refl a = a


{-
   We can also define `ap` for dependent functions.
-}

apd : {A : Set} {B : A → Set} (f : (x : A) → B x) → {x y : A} (p : x ≡ y) → tr p (f x) ≡ f y
-- tr refl (f x) ≡ f x
-- f x = f x
apd f refl = refl


