/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
A set of integers $A$ is Ramsey $2$-complete if, whenever $A$ is $2$-coloured, all sufficiently large integers can be written as a monochromatic sum of elements of $A$. Burr and Erdős [BuEr85] showed that there exists a constant $c>0$ such that it cannot be true that\[\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2\]for all large $N$ and that there exists a Ramsey $2$-complete $A$ such that for all large $N$\[\lvert A\cap \{1,\ldots,N\}\rvert < (2\log_2N)^3.\]Improve either of these bounds.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#54 : [Er95,p.172] number theory | ramsey theory The stated bounds are due to Burr and Erdős [BuEr85] . Resolved by Conlon, Fox, and Pham [CFP21] , who constructed a Ramsey $2$-complete $A$ such that\[\lvert A\cap \{1,\ldots,N\}\rvert \ll (\log N)^2\]for all large $N$. See also [55] and [843] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links This page was last edited 28 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #54, https://www.erdosproblems.com/54, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem54

/-- A two-colouring of the integers is represented by a map to the two-element type `Fin 2`. -/
def TwoColour : Type :=
  ℤ → Fin 2

/-- A positive finite sum from `A` is monochromatic when all of its summands have the same colour. -/
def IsMonochromaticSum (A : Set ℤ) (colour : TwoColour) (n : ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧
    ∃ x : Fin k → ℤ,
      (∀ i, x i ∈ A) ∧
      (∀ i j, colour (x i) = colour (x j)) ∧
      (∑ i, x i) = n

/-- The literal formalization of being Ramsey 2-complete: every two-colouring represents
all sufficiently large integers by monochromatic sums of elements of the set. -/
def IsRamseyTwoComplete (A : Set ℤ) : Prop :=
  ∀ colour : TwoColour, ∃ N₀ : ℤ, ∀ n : ℤ, N₀ ≤ n → IsMonochromaticSum A colour n

/-- The number of elements of `A` in the integer interval from `1` through `N`. -/
def countInInterval (A : Set ℤ) (N : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) (N : ℤ)).filter (fun z => z ∈ A)).card

/-- The asymptotic upper bound expressed by the notation `≪ (log N)^2` in the resolution.
The logarithm is taken in the natural real logarithm; changing its base only changes the
constant. -/
def HasQuadraticLogBound (A : Set ℤ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countInInterval A N : ℝ) ≤ C * (Real.log (N : ℝ)) ^ 2

/-- The requested improvement is the existence of a Ramsey 2-complete set satisfying the
quadratic-logarithmic counting bound. -/
def ImprovesEitherBound : Prop :=
  ∃ A : Set ℤ, IsRamseyTwoComplete A ∧ HasQuadraticLogBound A

/-- The resolved result attributed to Conlon, Fox, and Pham, recorded as a proposition so that
the deep external construction is an explicit input rather than an unproved Lean theorem. -/
def CFP21Claim : Prop :=
  ∃ A : Set ℤ, IsRamseyTwoComplete A ∧ HasQuadraticLogBound A

/-- The empty set has zero elements in every interval, providing a kernel-checked control for
the counting definition. -/
theorem countInInterval_empty (N : ℕ) : countInInterval (∅ : Set ℤ) N = 0 := by
  simp [countInInterval]

/-- The recorded Conlon--Fox--Pham result is exactly the formalized answer to the question. -/
theorem cfp21_claim_is_the_requested_improvement
    (h : CFP21Claim) : ImprovesEitherBound := by
  exact h

/-- The resolved claim supplies a Ramsey 2-complete set with the stated quadratic-logarithmic
bound. -/
theorem cfp21_exists_ramsey_set
    (h : CFP21Claim) :
    ∃ A : Set ℤ, IsRamseyTwoComplete A ∧ HasQuadraticLogBound A := by
  exact h

#print axioms countInInterval_empty
#print axioms cfp21_claim_is_the_requested_improvement
#print axioms cfp21_exists_ramsey_set

end ErdosProblem54