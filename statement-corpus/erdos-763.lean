/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $A\subseteq \mathbb{N}$. Can there exist some constant $c>0$ such that\[\sum_{n\leq N} 1_A\ast 1_A(n) = cN+O(1)?\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#763 : [Er65b] [Er70c] number theory | additive combinatorics A conjecture of Erdős and Turán. Erdős and Fuchs [ErFu56] proved that the answer is no in a strong form: in fact even\[\sum_{n\leq N} 1_A\ast 1_A(n) = cN+o\left(\frac{N^{1/4}}{(\log N)^{1/2}}\right)\]is impossible. The error term here was improved to $o(N^{1/4})$ by Jurkat (unpublished) and Montgomery and Vaughan [MoVa90] . See also [764] for a generalisation to more summands. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #763, https://www.erdosproblems.com/763, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open scoped BigOperators

-- @category research solved








open Classical Filter

namespace Erdos763

/-- The number of ordered representations of `n` as `a + b`, with both
summands in `A`.  This is the natural convolution `1_A * 1_A` on `ℕ`. -/
def convolutionCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1),
    if a ∈ A ∧ n - a ∈ A then 1 else 0

/-- The partial sum of the convolution counts through `N`, corresponding to
the source's sum over `n ≤ N`. -/
def convolutionPartialSum (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), convolutionCount A n

/-- Formalization of an `O(1)` error term: the difference from `cN` is
uniformly bounded for all natural numbers `N`.  Restricting to all `N` is
equivalent to eventual boundedness after enlarging the bound to cover the
finite initial segment. -/
def HasLinearBoundedError (A : Set ℕ) (c : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ N : ℕ,
      |(convolutionPartialSum A N : ℝ) - c * (N : ℝ)| ≤ K

/-- The question from the source, formalized as the existence of a set `A`
and a positive constant `c` whose convolution partial sums have bounded
error from `cN`. -/
def LinearRepresentationQuestion : Prop :=
  ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧ HasLinearBoundedError A c

/-- Proved sanity control: the empty set has identically zero convolution
count, exercising the definitions rather than merely asserting an arithmetic
identity unrelated to this artifact. -/
theorem empty_convolution_control (n : ℕ) :
    convolutionCount (∅ : Set ℕ) n = 0 := by
  simp [convolutionCount]

/-- Proved sanity control: the singleton `{0}` has exactly one ordered
representation of zero. -/
theorem singleton_zero_control :
    convolutionCount ({0} : Set ℕ) 0 = 1 := by
  simp [convolutionCount]

/-- Erdős--Fuchs' resolution of the question: no set of natural numbers and
positive constant can have convolution partial sums equal to `cN + O(1)`.

The source states the stronger impossibility of an error
`o(N^(1/4) / (log N)^(1/2))`; the present theorem records only the original
question's bounded-error conclusion. The proof of this deep analytic-number-
theoretic result remains an explicit formalization gap. -/
theorem no_linear_bounded_error :
    ¬ LinearRepresentationQuestion := by
  sorry

#print axioms empty_convolution_control
#print axioms singleton_zero_control

end Erdos763
