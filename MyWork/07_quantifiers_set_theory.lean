import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/-!
Please try to do this assignment entirely on your own. When you
submit your work, if you've done it entirely on your own, please
let us know with an associated text statement to that effect. We
will give you 5 points extra credit. This opportunity of course
assumed that everyone will be truthful, under the honor code.

You may work closely with up to two partners. If you do this, then
please (1) list all partners, including names and email ideas just
below, (2) attest truthfully to having worked closely on the whole
assigment with (no more than two) others, and as a group submit just
one copy of the group-completed assignment. You may NOT divide up
the work: everyone needs to work through every problem together.

Collaborators? List names and email id's here:


-/

/-! #1 [20 points] Reasoning about set membership (no proofs involved)

Suppose s, t, and r are sets of natural numbers, defined as follows.
-/

def s : Set Nat := { 0, 1, 2, 3, 4 } -- notation by enumeration
-- internally  this is simply 0 ∨ (1 ∨ (2 ∨ (3 ∨ 4)))
def t : Set Nat := { n | n = 3 \/ n = 4 \/ n = 5 }
-- actually this is same with {3, 4, 5}
def r : Set Nat := { n | ∃ m, n = m + 1 }
-- but set-builder notation can be more expressive

/-!
Use *display notations* to express the membership of each
of the following sets. Here's an example. You fill in to the
right of the :=. Then it's your turn.
-/


-- 0. s ∩ t -- intersection
def q0 : Set Nat := { 3, 4 }


-- 1. s ∩ r
def q1 : Set Nat := {1, 2, 3, 4}


/-!
For the remaining problems, you can write the whole definition.
Remember, use *display notation* in all your answers. We want to
see that you can figure out, on your own, what values are in each
of the specified sets.
-/


-- 2. q2 = s \ t -- set minus
def q2 : Set Nat := {0, 1, 2}

-- 3. q3 = t \ s
def q3 : Set Nat := {5}

-- 4. q4 = t × { 0, 1 } -- multiply
def q4 : Set (Nat × Nat) := {(3,0), (3,1), (4,0), (4,1), (5,0), (5,1)}

-- 5. q5 = 𝒫 t -- powerset, show the set of all subsets of t
def q5 : Set (Set Nat) := {∅, {3}, {4}, {5}, {3,4}, {3,5}, {4,5}, {3,4,5}}

/-!
#2 [20 points]

Prove that 5 is not a member of q0.

Remember two things: (1) 5 ∉ q0 means ¬(5 ∈ q0);
(2) that in turn means (5 ∈ q0) → False, which in
turn is an implication. You have to be able to do
this kind of reasoning on your own. Prove 5 ∉ q0
as an implication!
-/



-- Example: prove 5 ∉ q
example : 5 ∉ q0 :=
-- Proof by negation (negation introduction):
-- assume 5 ∈ h, derive contradiction, conclude ¬(5 ∈ h), i.e., 5 ∉ q.
(fun (h : 5 ∈ q0) =>
  (nomatch h)         -- by False elim (5 = 3 \/ 5 = 4 has no proof)
)



-- A [5 points]

-- Prove: 4 ∈ q0
example : 4 ∈ q0 :=
  Or.inr rfl


-- B [5 points]

-- Prove: 3 ∈ s ∩ t
example : 3 ∈ s ∩ t :=
  And.intro
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (Or.inl rfl)


-- a break down way
example : 3 ∈ s ∩ t := by
  apply And.intro
  · -- prove 3 ∈ s
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    rfl
  · -- prove 3 ∈ t
    apply Or.inl
    rfl


-- C [5 points]

-- Prove 0 ∉ r
example : 0 ∉ r :=
fun h => match h with
| ⟨m, h⟩ =>
  Nat.noConfusion (h.symm)

/-
1. The type 0 ∉ r is equivalent to (0 ∈ r) → False
2. We start with fun h => which assumes h : 0 ∈ r
3. By the definition of r, h contains evidence that there exists some m where 0 = m + 1
4. We pattern match on h to get m and the equality h : 0 = m + 1
5. h.symm gives us m + 1 = 0
6. Nat.noConfusion is used because we know that no successor number can equal 0
-/

example : 0 ∉ r :=
(
  fun h: (0 ∈ r) =>
  (nomatch h)
)

/-!
In addition to a formal proof, give a proof in English, explaining the
precise logical reasoning that leads to this conclusion. Start by stating
the underlying logical proposition that needs to be proved, and identify
explicitly the first step you must therefore take (what inference rule
you will apply) to construct a proof.

Here:
To prove 0 ∉ r, we need to show ¬(0 ∈ r), which means (0 ∈ r) → False.
Assume 0 ∈ r.
By the definition of r = {n | ∃ m, n = m + 1}, this means there exists some natural number m such that 0 = m + 1.
However, this is impossible because 0 is not a successor number (it cannot be equal to m + 1 for any m).
This contradiction proves that 0 ∉ r.

The key insight is that we're using the fundamental property of natural numbers
that 0 is not equal to any successor number (m + 1), which is what Nat.noConfusion captures in Lean.
-/



/-!
D [5 points]

You are to prove that the empty set is in the
powerset of t. Remember that the powerset of t
is the set of all subsets of t, including both
the empty, and the full, subsets of t. Clearly
the proposition is true. But what exactly is to
be proved, and how do you prove it?

The answer is that you just need to show that
∅ is a subset of t! This is how you'd proceed
in a natural language proof description. Ok, so
now what's required to show ∅ ⊆ t? You need to
remind yourself what it means for one set, a,
to be subset of another, b.

That challenge with proofs like this one in set
theory is to see how set theoretical propositions
reduce to propositions in predicate logic. Just
prove the corresponding logical proposition.

Use top-down proof construction. Once you remember
the definition of *subset* you should see just how
to start.
-/

example : ∅ ∈ 𝒫 t :=
fun x h => by cases h
-- By definition of subset, ∅ ⊆ t means: ∀ x, x ∈ ∅ → x ∈ t
-- The proof starts with fun x h where:
--  1. x is an arbitrary element
--  2. h is the assumption that x ∈ ∅
-- cases h tries to consider all possible ways that x could be in the empty set
-- Since there are no possible cases (the empty set has no elements), this completes the proof

example : ∅ ∈ 𝒫 t :=
Set.empty_subset t

/-!
Now give a corresponding English-language proof. Here:

Prove: ∅ ∈ 𝒫 t
Proof: To show that ∅ ∈ 𝒫 t (which is the set of all
subsets of t) we need to show that ∅ (the empty set)
is a subset of t. By the definition of subset, what we
thus need to show is ___. [Proceed from here]. To prove
that we first ...
-/



/-! #3 [30 points]

Formally prove (t \ { 5 }) ⊆ s.

Here we ask you first to understand most of the
formal proof and then to finish it off given that
you understand it and you see how to finish off two
small remaining proofs at the end of the day.

To help you understand how to reason in this case,
we first explain that \ show that for any n, if n ∈ (t \ { 5 })
then n ∈ s. Before you go on make absolutely sure
you fully understand why this is what needs to be
proved. Go back again if you need to and read and
understand the formal specification of the subset
operator; then prove that that underlying logical
proposition holds in this case. You'll need to see
that at top level, you must prove a ∀ proposition;
then you must prove a → proposition. You need to
remember that proofs of each involve first making
an assumption, and then showing that the conclusion
follows in that context.

-/

example : (t \ { 5 }) ⊆ s :=
-- by the definition of ⊆ what is to be proved is every element of t except 5 is the element of s
-- The first step is ∀ introduction: assume n is an arbitary natural number
(fun (n : Nat) =>
  -- The next step is → introduction: assume  n ∈ n ∈ (t \ { 5 })
  (fun (h : n ∈ (t \ { 5 })) =>
  -- Now in that context, what remains to prove is that n ∈ s
  -- to do this requires *using* the proof of h to make progress
  -- understand and use fact that h is a proof of a conjunction (why?)
  -- if you don't see why review the formal definition of ⊊ (proper subset)
    (
      -- from h we can derive l : n ∈ t by And elimination
      let l := And.left h
      -- We have thus deduced, l, that n ∈ {3, 4, 5}
      -- We know that l is a proof of a disjunction
      -- We finish the proof by case analysis on *l*
      Or.elim l
        -- case n = 3
        (fun neq3 =>
          -- here we rewrite the goal, n ∈ s, to 3 ∈ s, knowing n = 3
          --
          (by  -- given that n = 3 in this case, rewrite goal as 3 ∈ s
            rw [neq3]
            -- and finally prove this by Or.introduction
            exact (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          )
        )
        -- case n = 4 \/ n = 5
        -- proof by cases analysis again
        (fun mem45 =>
          (match mem45 with
          -- case where n = 4
          | Or.inl four =>
            (by
              rw [four]
              exact (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
            )   -- use the same method as used to show 3 ∈ s
          -- case where n = 5
          | Or.inr five =>
            (by
              rw [five]
              exact absurd five (And.right h)
            )
            -- the final step uses a different axiom to finish it up
          )
        )
    )
  )
)

/-! #4 [15 points]

Provide a detailed English-language proof of the proposition
in the preceding problem: (t \ { 5 }) ⊆ s. Use the commented
formal proof as a basis for writing a proof in English. Make
sure you refer to specific proof techniques (which axioms of
logic are you employing) at each level of English language
proof. Here's a way to get started.

Problem: Prove (t \ { 5 }) ⊆ s.

Proof. By the definition of ⊆ what we need to prove is that
∀ (n : Nat), n ∈ (t \ { 5 }) → n ∈ s. We begin by assuming
first that n is some arbitrary natural number (∀ intro). We
next, by → intro, assume that n ∈ (t \ { 5 }). In the context
of these assumptions our remaining goal is to prove n ∈ s.
The proof of this proposition is by ... [hint: look at the
formal proof!]
-/


/-
By the definition of ⊆ what we need to prove is that
∀ (n : Nat), n ∈ (t \ { 5 }) → n ∈ s.
We begin by assuming first that n is some arbitrary natural number (∀ intro).
We next, by → intro, assume that n ∈ (t \ { 5 }).
In the context of these assumptions our remaining goal is to prove n ∈ s.

The proof of this proposition is by case analysis.
First, note that our assumption n ∈ (t \ { 5 }) gives us two facts by And elimination:
1. n ∈ t (call this l)
2. n ∉ {5} (call this r)

Since n ∈ t, we know by the definition of t that n = 3 ∨ n = 4 ∨ n = 5.
We proceed by Or elimination on this disjunction:
Case 1: If n = 3
- By rewriting with n = 3, our goal becomes 3 ∈ s
- This is true by direct membership in s (can be proved by Or introduction)
Case 2: If n = 4 ∨ n = 5
We perform another Or elimination:

Subcase 2a: If n = 4
- By rewriting with n = 4, our goal becomes 4 ∈ s
- This is true by direct membership in s (can be proved by Or introduction)

Subcase 2b: If n = 5
- This case leads to a contradiction because:
- From r we have n ∉ {5}
- But n = 5 implies n ∈ {5}
- This contradiction completes this case

Since we've covered all possible cases and shown that in each possible case
(except the contradictory one), n ∈ s, we've proved that (t \ { 5 }) ⊆ s
-/
