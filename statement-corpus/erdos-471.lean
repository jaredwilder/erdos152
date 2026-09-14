/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Given a finite set of primes $Q=Q_0$, define a sequence of sets $Q_i$ by letting $Q_{i+1}$ be $Q_i$ together with all primes formed by adding three distinct elements of $Q_i$. Is there some initial choice of $Q$ such that the $Q_i$ become arbitrarily large?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#471 : [ErGr80,p.94] number theory A problem of Ulam. In particular, what about $Q=\{3,5,7,11\}$? Mrazović and Kovač, and independently Alon, have observed that the existence of some valid choice of $Q$ follows easily from Vinogradov's theorem that every large odd integer is the sum of three distinct primes. In particular, there exists some $N$ such that every prime $>N$ is the sum of three distinct (smaller) primes. We may then take $Q_0$ to be the set of all primes $\leq N$ (in which case all primes are eventually in some $Q_i$). Additional thanks to : Noga Alon, Rudi Mrazovic, and Vjekoslav Kovac Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links ( View history ) View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #471, https://www.erdosproblems.com/471, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos471

/-- A natural number is addable to `Q` when it is prime and is the sum of
three pairwise distinct members of `Q`. -/
def addable (Q : Finset ℕ) (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p = a + b + c

/-- The next set in the Ulam process. The finite range is sufficient because
every represented sum is at most three times the sum of the elements of `Q`. -/
def qStep (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ (Finset.range (3 * Q.sum id + 1)).filter (addable Q)

/-- The set `Q_i` obtained after `i` applications of the process, starting
from `Q`. -/
def qIter (Q : Finset ℕ) : ℕ → Finset ℕ
  | 0 => Q
  | n + 1 => qStep (qIter Q n)

/-- The formal version of the question: the initial finite set consists only
of primes, and the cardinalities of its iterates are unbounded. -/
def UlamQuestion : Prop :=
  ∃ Q : Finset ℕ,
    (∀ p ∈ Q, Nat.Prime p) ∧
      ∀ B : ℕ, ∃ i : ℕ, B ≤ (qIter Q i).card

/-- The explicit number-theoretic input described in the resolution: beyond
some threshold, every prime has a representation as a sum of three distinct
smaller primes. -/
def LargePrimeThreeSum : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → N < p →
    ∃ a b c : ℕ,
      Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧
        a < p ∧ b < p ∧ c < p ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        p = a + b + c

/-- A basic anti-vacuity control: with no initial elements, no new prime can
be formed, so the process really uses the three-element formation rule. -/
theorem qStep_empty : qStep (∅ : Finset ℕ) = ∅ := by
  simp [qStep, addable]

/-- A second computed control: a singleton cannot produce a sum of three
pairwise distinct elements, so its first iterate is unchanged. -/
theorem qStep_singleton : qStep ({2} : Finset ℕ) = ({2} : Finset ℕ) := by
  simp [qStep, addable]

/-- The resolution of Erdős problem 471, under the explicitly stated
Vinogradov-type input. The remaining gap is the induction showing that the
initial set of all primes at most the threshold eventually contains every
prime; this is not hidden behind an axiom and is recorded honestly as `sorry`.

SOURCE-to-formal mapping: the source asks whether some finite prime set has
arbitrarily large iterates, which is `UlamQuestion`. The known resolution says
that `LargePrimeThreeSum` supplies such an initial set. -/
theorem vinogradov_resolution :
    LargePrimeThreeSum → UlamQuestion := by
  sorry

#print axioms qStep_empty
#print axioms qStep_singleton

end Erdos471
