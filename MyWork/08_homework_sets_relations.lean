import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Cs2120f24.Library.setTheory.«03_properties_of_relations»

set_option diagnostics true
/-
Homework #8 Properties of Relations

You must be able to do this homework on your own.
If getting to that point requires collaboration, you
may collaborate with up to two other people. In this
case, you are to hand in one assignment with the names
and email addresses of all the collaborators. Each
collaborator must work with every other one on this
assignment. You may not just split the problems one
or two for each person.
-/

/-!
We've importd all of the definitions of properties of relations
from 03_properties_of_relations so you can use them here with no
problem. Use View > Editor Layout > Split Down to have two panes
open, one looking at the property definitions file and one open
on this one.

PREREQUISITE: Thoroughly study lecture 7, files 1, 2, and 3, on
sets, relations, and properties of relations. Remember, you cannot
learn to construct proofs by just reading Lean proof terms. You
really have to construct them on your own. So where we give you
proofs, *copy them into a comment, then delete them, then build
them back, cheating by looking at the saved comment if you must*.
-/

-- NOTE:
-- Rel α β is just a fancy way to write a relationship between two types
-- It's basically a function that takes two inputs (of type α and β)
-- and returns true or false
-- For example, if α is String and β is Nat,
-- then Rel String Nat would be a relationship between strings and numbers

-- This is a relation between numbers: "is less than"
def lessThan : Rel Nat Nat := fun a b => Nat.lt a b

-- Add decidability instance
instance (a b : Nat) : Decidable (lessThan a b) :=
  match a, b with
  | a, b => Nat.decLt a b

#eval lessThan 3 5  -- Should output "true"
#eval lessThan 5 3  -- Should output "false"

/-
PROBLEM #1 [25 points]. We've see that, in Lean, every function
of type α → β is total. Any such function in Lean must be defined
*for all* values of the intput type, α. If you fail to provide an
output value for every input, Lean will tell you you're "missing
cases." It's super-important in constructive logic that functions
are total because we use them to prove universal generalizations!
To prove ∀ (x : α), P x, we define a function from (x : α) to P x.
The reason a function proves a universal proposition is that every
function in constructive logic is required to be total.

We can turn any function, f, in Lean into a binary relation by
specifying the relations' membership predicate to be nothing
other than (fun a b => b = f a). This says that a pair, (a, b)
is in this relation for a function f exactly when b = f a.

Here's a function, funToRel, that takes any function from any type,
α to any type β, and that returns the corresponding binary relation
with this membership predicate. To be absolutely clear, funToRel takes
two types, α and β (implicitly), and any function, f : α → β, and it
returns a binary relation from α to β, specified by its membership
predicate, as stated.
-/

def funToRel { α β : Type} : (f : α → β) → Rel α β :=
  fun f => fun a b => f a = b

-- NOTE: Rel α β is a type synonym for α → β → Prop (a binary relation)
-- Takes a function f
-- Takes two values a (of type α) and b (of type β)
-- Returns the proposition f a = b

-- Example with successor function
def succFun : Nat → Nat := Nat.succ
def succ_Rel := funToRel succFun

-- These are equivalent:
#eval succFun 1        -- returns 2
#reduce (types:=true) succ_Rel 1 2      -- returns true (because succFun 1 = 2)
#reduce (types:=true) succ_Rel 1 3      -- returns false (because succFun 1 ≠ 3)

/-!
Now we can propose, and you are to complete the proof,
that every relation obtained from any function (using
funToRel) has the property of being total, as defined
by our isTotal predicate on binary relations. We give a
good amount of the proof in English, and a little bit
of it in Lean. You finish the missing formal parts.
-/
-- NOTE: Think of it as: "Every input MUST have at least one output"
-- For funToRel f, we need to show that for any a : α,
-- there exists some b : β where funToRel f a b is true.
example {α β : Type} (f : α → β) : isTotalRel (funToRel f) :=
/-
by the definition of total, what is to be proved is that
∀ (x : α), ∃ (y : β), r x y. We first assume an arbitrary
input value a, then we show there exists a corresponding
output value such that the pair is in the relation. Just
a little thought produces (f a) as the witness, as it is
exactly the value that corresponds to the input, a. Then
we need to prove ((funToRel f) a (f a)). By the definition
of funToRel we need to show that (a, (f a)) is in the
relation but that requires exactly that the output, f a,
is equal to f applied to the input, a, i.e., f a = f a.
-/
fun a => -- assume arbitrary a : α
  Exists.intro -- prove ∃ b, funToRel f a b
  (f a)  -- NOTE: witness: the function output for input a
  (rfl)  -- NOTE: proof that f a = f a (reflexivity)
  -- the Rel we need to prove is f a = b (defined by funToRel)


/-!d
PROBLEM #2 [25 points]

We repeat here the definition of the bank account
number relation from the relations.lean file. Here
you are to state and prove the proposition that this
relation is not single-valued.
-/

def acctsOf : Rel String Nat := fun s n =>
  s = "Mary" ∧ n = 1 ∨ -- Mary has account #1
  s = "Mary" ∧ n = 2 ∨ -- Mary also has account #2
  s = "Lu"   ∧ n = 3  -- Lu has account #3


-- NOTE: Recall single valued: For each input x, there can only be ONE output
-- def isSingleValuedRel (r : Rel α β) : Prop := ∀ x y z, r x y → r x z → y = z
-- This means if x is related to y and x is related to z, then y must equal z.

example : ¬isSingleValuedRel acctsOf :=
-- assume acctsOf is single valued:
fun (h : isSingleValuedRel acctsOf) =>
-- show that that implies 1 = 2
-- as that's absurd, conclude ¬isSingleValued acctsOf
(
  -- ∀ x y z, r x y → r x z → y = z

  -- First get proofs that ("Mary",1) and ("Mary", 2) are in acctsOf
  -- NOTE: Show Mary has account #1
  let a1 : acctsOf "Mary" 1 := Or.inl ⟨ rfl, rfl ⟩
  -- NOTE: Show Mary has account #2
  let a2 : acctsOf "Mary" 2 := Or.inr (Or.inl ⟨ rfl, rfl ⟩)

  -- You should see that that contradicts h
  -- Now use h to derive an evident contradiction
  let contra := h "Mary" 1 2 a1 a2
  -- And show that that can't possibly be
  -- Allowing you to conclude that h can't be true so ¬h must be
  by contradiction  -- shows 1 ≠ 2
)

/-!
PROBLEM #3 [25 points]

State formally and prove the proposition that the
successor relation on natural numbers (Nat.succ) is
an injective function. You can use funToRel applied
to Nat.succ to define that relation if you want.
-/

def succRel := funToRel Nat.succ
-- NOTE: So succRel n m means Nat.succ n = m

#reduce (types:=true) succRel 1 2
-- reduces to the proposition Nat.succ 1 + = 2, i.e., 2 = 2

example : succRel 1 2 := rfl

--NOTE: Recall isInjective
-- def isInjective (r : Rel α β) : Prop :=
--   isSingleValuedRel r ∧                    -- First conjunct
--   ∀ x y z, r x z → r y z → x = y          -- Second conjunct
-- This means every input has a different output.
-- If they have the same output, then they are the same input.
-- HERE
example : isInjective succRel :=
And.intro
  --NOTE: First part (single-valued):
  -- succRel is a singleValued relation (a function)
  -- - Takes a b c and proofs hab : succRel a b and hac : succRel a c
  -- - hab means Nat.succ a = b
  -- - hac means Nat.succ a = c
  -- - Rewrites b with Nat.succ a and c with Nat.succ a
  -- - Results in Nat.succ a = Nat.succ a, which is true by reflexivity
  (fun a b c hab hac =>
    -- note that hab and hac are proofs of Nat.succ a = b and Nat.succ a = c
    -- rewrite goal from b = c to a.succ = b.succ hab and hac (right to left)
    -- that leaves a.succ = a.succ, which rw proves by the reflexivity of =
    by rw [←hab, ←hac]    -- the ← means rewrite right hand in goal with left
  )
  -- succRel is an injective relation
  -- NOTE: Second part (injective):
  -- - Takes a b c and proofs hab : succRel a b and hbc : succRel c b
  -- - hab means Nat.succ a = b
  -- - hbc means Nat.succ c = b
  -- - Rewriting gives Nat.succ a = Nat.succ c
  -- - Nat.succ.inj is a theorem that says if Nat.succ x = Nat.succ y then x = y
  -- - Therefore a = c
  (fun a b c hab hbc =>
  -- If Nat.succ a = b and Nat.succ c = b, then a = c
    Nat.succ.inj (by rw [hab, hbc])
  )   -- ok, you have to prove the rest


/-!
PROBLEM #4 [25 points]

A. Given (non-zero) natural numbers a, b, and n, we
say that a is congruent to b mod n if a mod n = b mod n.
Complete the following definition of the binary relation,
congruence mod n.
-/

def congruentModN (n : Nat) : Rel Nat Nat := fun a b => a % n = b % n

/- NOTE:
- This says a is congruent to b modulo n
- if they have the same remainder when divided by n
- Example: 8 ≡ 12 (mod 4) because 8 % 4 = 0 and 12 % 4 = 0
-/

-- Test cases will succeed when you give the right definition
example : congruentModN 4 8 12 := rfl
example : congruentModN 5 25 50 := rfl
example : ¬congruentModN 4 4 9 := fun h => nomatch h


/-!
Now prove the proposition that congruence mod n is an equivalence relation
-/
example (n : Nat) : @isEquivalence Nat Nat (congruentModN n) :=
/-
By the definition of equivalence, what we need to show is that the
relation is reflexive, symmetric, and transitive.
-/

/-
NOTE: Recall equivalence

def isEquivalence {α : Type} (r : Rel α α) : Prop :=
  isReflexive r ∧ (isSymmetric r ∧ isTransitive r)

def isReflexive {α : Type} (r : Rel α α) : Prop :=
  ∀ a, r a a
-- For every element a, a is related to itself

def isSymmetric {α : Type} (r : Rel α α) : Prop :=
  ∀ a b, r a b → r b a
-- If a is related to b, then b is related to a

def isTransitive {α : Type} (r : Rel α α) : Prop :=
  ∀ a b c, r a b → r b c → r a c
-- If a is related to b and b is related to c, then a is related to c
-/

-- Destructure first ∧
And.intro
  -- Left: prove (congruentModN n) is reflexive
  -- NOTE: Reflexive (∀ a, R a a):
  -- a % n = a % n
  (
    fun a => rfl
  )
  -- Right: Destructure second ∧
  (
    And.intro
      -- Left: Prove (congruentModN n) is symmetric
      /-
      - Takes h : a % n = b % n
      - Returns b % n = a % n (symmetry of equality)
      - This proves ∀ a b, congruentModN n a b → congruentModN n b a
      -/
      (fun a b h => Eq.symm h)

      -- Prove (congruentModN n) is transitive
      /-
      - Takes hab : a % n = b % n and hbc : b % n = c % n
      - Returns a % n = c % n (transitivity of equality)
      - This proves ∀ a b c,
      - congruentModN n a b → congruentModN n b c → congruentModN n a c
      -/
      (fun a b c hab hbc => Eq.trans hab hbc)
  )


-- NOTE: diff between false.elim and nomatch
-- Using false.elim
example (h : False) : 0 = 1 :=
  False.elim h

-- Using nomatch
example : ¬(0 = 1) :=
  fun h => nomatch h
