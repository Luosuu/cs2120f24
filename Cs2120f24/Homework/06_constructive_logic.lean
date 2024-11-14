namespace cs2120f24.constructiveLogic

/-! HOMEWORK #6. COUNTS FOR TWO ASSIGNMENTS.

This is an important homework. It gives you an
opportunity to work out many of the kinks in your
understanding of predicate logic and deductive
proofs in type theory. With P, Q, and R accepted
as propositions, you are to give proofs of all of
the identities from Library/propLogic/identities,
which I've rewritten in Lean for you. There's one
of these axioms that has no constructive proof (in
just one direction). You can just identify it.
-/


-- Suppse P, Q, and R are arbitrary propositions
axiom P : Prop
axiom Q : Prop
axiom R : Prop

/-!
Give proofs in Lean that each of the following identities
is valid. We already know they're classically valid as we
validated their propositional logic analogics semantically
using our model / validity checker. To get you started with
a concrete example, we prove the first one for you and give
a little English explanation after. You should od the same
for each proposition you prove.
-/


def andIdempotent   : P ↔ (P ∧ P) :=
Iff.intro
  -- forward direction: P → P ∧ P
  -- assume p : P, show P ∧ P
  (fun (p : P) => (And.intro p p))
  -- backwards direction: P ∧ P → P
  (fun (h : And P P) => (h.right))

/-!
In English. We are to show that any proposition
P is equivalent to P ∧ P. By the Iff.intro axiom,
it will suffice to first prove P → P ∧ P and then
to prove P ∧ P → P. With that we'll be done.

Proof of forward direction: P → P ∧ P. Assume we
have a proof (p : P). Then applying the axiom
of And introduction to p and p, we can derive the
proof of P ∧ P that will show that if P is true,
then P ∧ P is true. So P → P ∧ P.

Proof of backward direction. P ∧ P → P. Assume
we have a proof, pandp : P ∧ P. By either one of
the two elimination axioms we can derive a proof
of p: as either pandp.left or pandp.right.
-/

def orIdempotent : P ↔ (P ∨ P) :=
Iff.intro
  -- forward direction: P → (P ∨ P)
  (fun (p : P) => Or.inl p)
  -- backward direction: (P ∨ P) → P
  (fun (p : P ∨ P) =>
    Or.elim p
      (fun hp : P => hp)
      (fun hp : P => hp))
/-
English explanation: To prove P ↔ (P ∨ P), we need to show both directions.
- Forward (P → P ∨ P): Given a proof p of P, we can use Or.inl to inject it into the left side of the disjunction.
- Backward (P ∨ P → P): Given P ∨ P, we use Or.elim to handle both cases. In either case, we get P directly.
-/

def andCommutative : (P ∧ Q) ↔ (Q ∧ P) :=
Iff.intro
  -- forward direction: (P ∧ Q) → (Q ∧ P)
  (fun pq : P ∧ Q => And.intro pq.right pq.left)
  -- backward direction: (Q ∧ P) → (P ∧ Q)
  (fun qp : Q ∧ P => And.intro qp.right qp.left)
/-
English explanation: For P ∧ Q ↔ Q ∧ P:
- Forward: Given P ∧ Q, we extract both components and reconstruct them in reverse order.
- Backward: Similarly, given Q ∧ P, we extract and reconstruct in reverse order.
-/


def orCommutative : (P ∨ Q) ↔ (Q ∨ P) :=
Iff.intro
  (fun pq : P ∨ Q =>
    Or.elim pq
      (fun p : P => Or.inr p)  -- If we have P, put it on the right
      (fun q : Q => Or.inl q)) -- If we have Q, put it on the left
  (fun qp : Q ∨ P =>
    Or.elim qp
      (fun q : Q => Or.inr q)  -- If we have Q, put it on the right
      (fun p : P => Or.inl p)) -- If we have P, put it on the left
/-
English explanation:
- Forward direction (P ∨ Q → Q ∨ P):
Given P ∨ Q, we must handle both possibilities
If we have P, we use Or.inr to put it on the right side of Q ∨ P
If we have Q, we use Or.inl to put it on the left side of Q ∨ P
Backward direction (Q ∨ P → P ∨ Q) works similarly but in reverse
-/


def identityAnd : (P ∧ True) ↔ P :=
Iff.intro
  (fun pt : P ∧ True => pt.left)  -- Extract P from P ∧ True
  (fun p : P => And.intro p True.intro)  -- Pair P with True
/-
English explanation:
- Forward direction (P ∧ True → P):
Given P ∧ True, we can just extract P using .left
The True part is irrelevant
Backward direction (P → P ∧ True):
Given P, we need to construct P ∧ True
We can always construct True using True.intro
Then pair P with True using And.intro
-/


def identityOr : (P ∨ False) ↔ P :=
Iff.intro
  (fun pf : P ∨ False =>
    Or.elim pf
      (fun p : P => p)  -- If P, return P
      (fun f : False => False.elim f))  -- False case impossible
  (fun p : P => Or.inl p)  -- Put P on left side of ∨
/-
English explanation:
- Forward direction (P ∨ False → P):
Given P ∨ False, we must handle both cases
If we have P, we return it
If we have False, we can derive anything (ex falso quodlibet)
Backward direction (P → P ∨ False):
Given P, we just inject it to the left side of the disjunction
-/


def annhilateAnd : (P ∧ False) ↔ False :=
Iff.intro
  (fun pf : P ∧ False => pf.right)  -- Extract False from conjunction
  (fun f : False => False.elim f)    -- From False, prove anything
/-
English explanation:
- Forward direction (P ∧ False → False):
Given P ∧ False, we can extract False using .right
We don't need P at all
Backward direction (False → P ∧ False):
Given False, we can prove anything (ex falso quodlibet)
This includes P ∧ False
-/


def annhilateOr : (P ∨ True) ↔ True :=
Iff.intro
  (fun _ => True.intro)  -- Always return True proof
  (fun _ => Or.inr True.intro)  -- Inject True to right side
/-
English explanation:
- Forward direction (P ∨ True → True):
Given P ∨ True, we don't even need to check which case we have
We can always construct True using True.intro
Backward direction (True → P ∨ True):
Given True, we inject it to the right side of the disjunction
We use Or.inr because we're putting it on the right side
-/


def orAssociative : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) :=
Iff.intro
  (fun pqr : (P ∨ Q) ∨ R =>
    Or.elim pqr
      (fun pq : P ∨ Q =>
        Or.elim pq
          (fun p : P => Or.inl p)  -- P case: put on far left
          (fun q : Q => Or.inr (Or.inl q)))  -- Q case: put in middle
      (fun r : R => Or.inr (Or.inr r)))  -- R case: put on far right
  (fun pqr : P ∨ (Q ∨ R) =>
    Or.elim pqr
      (fun p : P => Or.inl (Or.inl p))  -- P case: put on far left
      (fun qr : Q ∨ R =>
        Or.elim qr
          (fun q : Q => Or.inl (Or.inr q))  -- Q case: put in middle
          (fun r : R => Or.inr r)))  -- R case: put on right
/-
English explanation:
Forward direction ((P ∨ Q) ∨ R → P ∨ (Q ∨ R)):
- We must handle three cases: P, Q, and R
- For P: inject it to the leftmost position
- For Q: put it in the middle (right of first ∨, left of second)
- For R: put it on the far right
Backward direction (P ∨ (Q ∨ R) → (P ∨ Q) ∨ R):
- Again handle three cases
- For P: put it on far left inside another left
- For Q: put it on right of first disjunction
- For R: put it on the far right
-/


def andAssociative : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
Iff.intro
  (fun pqr : (P ∧ Q) ∧ R =>
    And.intro
      pqr.left.left           -- Extract P
      (And.intro              -- Make Q ∧ R
        pqr.left.right        -- Extract Q
        pqr.right))           -- Extract R
  (fun pqr : P ∧ (Q ∧ R) =>
    And.intro
      (And.intro              -- Make P ∧ Q
        pqr.left              -- Extract P
        pqr.right.left)       -- Extract Q
      pqr.right.right)        -- Extract R


def distribAndOr : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) :=
Iff.intro
  (fun pqr : P ∧ (Q ∨ R) =>
    Or.elim pqr.right
      (fun q : Q => Or.inl (And.intro pqr.left q))  -- P ∧ Q case
      (fun r : R => Or.inr (And.intro pqr.left r))) -- P ∧ R case
  (fun pqpr : (P ∧ Q) ∨ (P ∧ R) =>
    Or.elim pqpr
      (fun pq : P ∧ Q => And.intro pq.left (Or.inl pq.right))
      (fun pr : P ∧ R => And.intro pr.left (Or.inr pr.right)))
/-
English explanation:
Forward direction (P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)):
- We have P and (Q ∨ R)
- For Q case: combine P with Q to make P ∧ Q, put on left
- For R case: combine P with R to make P ∧ R, put on right
Backward direction ((P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)):
- For P ∧ Q case: extract P and Q, make P ∧ (Q ∨ R)
- For P ∧ R case: extract P and R, make P ∧ (Q ∨ R)
-/


def distribOrAnd : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) :=
Iff.intro
  (fun pqr : P ∨ (Q ∧ R) =>
    Or.elim pqr
      (fun p : P => And.intro (Or.inl p) (Or.inl p))  -- P case
      (fun qr : Q ∧ R =>
        And.intro (Or.inr qr.left) (Or.inr qr.right))) -- Q ∧ R case
  (fun pqpr : (P ∨ Q) ∧ (P ∨ R) =>
    Or.elim pqpr.left
      (fun p : P => Or.inl p)  -- P case from first disjunct
      (fun q : Q =>
        Or.elim pqpr.right
          (fun p : P => Or.inl p)  -- P case from second disjunct
          (fun r : R => Or.inr (And.intro q r))))  -- Q ∧ R case
/-
English explanation:
Forward direction (P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)):
- For P case: use P in both conjuncts
- For Q ∧ R case: split Q and R into separate disjunctions with P
Backward direction ((P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)):
- Need to handle all combinations of P, Q, and R
- If we have P in either disjunct, use that
- Otherwise, combine Q and R into Q ∧ R
-/


def equivalence : (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
Iff.intro
  (fun pq : P ↔ Q => And.intro pq.mp pq.mpr)  -- Extract both implications
  (fun pqp : (P → Q) ∧ (Q → P) =>
    Iff.intro pqp.left pqp.right)  -- Combine implications
/-
English explanation:
Forward direction (P ↔ Q → (P → Q) ∧ (Q → P)):
- Extract mp (modus ponens) for P → Q
- Extract mpr (modus ponens reverse) for Q → P
- Combine with And.intro
Backward direction ((P → Q) ∧ (Q → P) → P ↔ Q):
- Take both implications
- Use Iff.intro to create bi-implication
-/


def implication : (P → Q) ↔ (¬P ∨ Q) :=
Iff.intro
  -- forward direction requires classical logic
  (fun pq : P → Q => sorry)  -- This direction needs Classical.em
  -- backward direction
  (fun npq : ¬P ∨ Q =>
    fun p : P =>
      Or.elim npq
        (fun np : ¬P => False.elim (np p))
        (fun q : Q => q))


def exportation : ((P ∧ Q) → R) ↔ (P → Q → R) :=
Iff.intro
  (fun pqr : (P ∧ Q) → R =>
    fun p : P =>
      fun q : Q =>
        pqr (And.intro p q))  -- Combine P and Q, then apply original function
  (fun pqr : P → Q → R =>
    fun pq : P ∧ Q =>
        pqr pq.left pq.right)  -- Split conjunction and apply curried function
/-
English explanation:
Forward direction ((P ∧ Q) → R → (P → Q → R)):
- Take function expecting P ∧ Q
- Return curried function taking P, then Q
- Inside, reconstruct P ∧ Q and apply original function
Backward direction ((P → Q → R) → (P ∧ Q) → R):
- Take curried function
- Take P ∧ Q
- Split conjunction and apply curried function
-/


def absurdity : (P → Q) ∧ (P → ¬Q) → ¬P :=
fun h : (P → Q) ∧ (P → ¬Q) =>
  fun p : P =>
    (h.right p) (h.left p)
/-
English explanation:
- This proves that if P implies both Q and ¬Q, then P must be false
- Given P → Q and P → ¬Q (as h.left and h.right)
- To prove ¬P, we assume P and derive a contradiction
- Apply h.left to p to get Q
- Apply h.right to p to get ¬Q
- Apply ¬Q to Q to get a contradiction
- This shows P leads to a contradiction, thus ¬P
-/

def distribNotAnd : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) :=
Iff.intro
  (fun npq : ¬(P ∧ Q) =>
    match Classical.em P with
    | Or.inl p =>           -- If P is true
      match Classical.em Q with
      | Or.inl q => False.elim (npq (And.intro p q))  -- If Q also true, contradiction
      | Or.inr nq => Or.inr nq  -- If Q false, use ¬Q
    | Or.inr np => Or.inl np)   -- If P false, use ¬P
  (fun npnq : ¬P ∨ ¬Q =>
    fun pq : P ∧ Q =>
      Or.elim npnq
        (fun np : ¬P => np pq.left)   -- Use ¬P with P from P ∧ Q
        (fun nq : ¬Q => nq pq.right))  -- Use ¬Q with Q from P ∧ Q

/-
English explanation:
Forward direction (¬(P ∧ Q) → (¬P ∨ ¬Q)):
- This direction requires classical logic (law of excluded middle)
- Use Classical.em to decide if P is true or false
- If P is false, we have ¬P, so return that
- If P is true, use Classical.em again on Q
- If Q is false, we have ¬Q, so return that
- If both are true, we have a contradiction with our assumption ¬(P ∧ Q)
Backward direction ((¬P ∨ ¬Q) → ¬(P ∧ Q)):
- Given ¬P ∨ ¬Q and P ∧ Q
- If we have ¬P, use it with P from P ∧ Q to get contradiction
- If we have ¬Q, use it with Q from P ∧ Q to get contradiction
-/

def distribNotOr : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
Iff.intro
  (fun npq : ¬(P ∨ Q) =>
    And.intro
      (fun p : P => npq (Or.inl p))  -- Prove ¬P
      (fun q : Q => npq (Or.inr q))) -- Prove ¬Q
  (fun npnq : ¬P ∧ ¬Q =>
    fun pq : P ∨ Q =>
      Or.elim pq
        (fun p : P => npnq.left p)   -- Use ¬P
        (fun q : Q => npnq.right q))  -- Use ¬Q
/-
English explanation:
Forward direction (¬(P ∨ Q) → (¬P ∧ ¬Q)):
- To prove ¬P: assume P, inject it into P ∨ Q, contradiction with ¬(P ∨ Q)
- To prove ¬Q: assume Q, inject it into P ∨ Q, contradiction with ¬(P ∨ Q)
- Combine these with And.intro
Backward direction ((¬P ∧ ¬Q) → ¬(P ∨ Q)):
- Given P ∨ Q, use Or.elim to handle both cases
- If P, use ¬P to get contradiction
- If Q, use ¬Q to get contradiction
-/


/-!
EXTRA CREDIT: apply the axiom of the excluded middle
to give a classical proof of any propositions that you
identified as having no constructive proof. The axiom
is available as Classical.em (p : Prop) : p ∨ ¬p.
-/

#check Classical.em
-- Classical.em (p : Prop) : p ∨ ¬p
-- Given any proposition p, you can have a proof of p ∨ ¬p
-- You then have two cases: one with a proof of p, one with ¬p
example (A : Prop) : A ∨ ¬A := Classical.em A

def implication_classical : (P → Q) ↔ (¬P ∨ Q) :=
Iff.intro
  (fun pq : P → Q =>
    match Classical.em P with
    | Or.inl p => Or.inr (pq p)
    | Or.inr np => Or.inl np)
  (fun npq : ¬P ∨ Q =>
    fun p : P =>
      Or.elim npq
        (fun np : ¬P => False.elim (np p))
        (fun q : Q => q))
