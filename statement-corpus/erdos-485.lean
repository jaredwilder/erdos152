/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(k)$ be the minimum number of terms in $P(x)^2$, where $P\in \mathbb{Q}[x]$ ranges over all polynomials with exactly $k$ non-zero terms. Is it true that $f(k)\to\infty$ as $k\to \infty$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#485 : [Er61] [Ha74] [Er80,p.112] analysis | polynomials This is Problem 4.4 in [Ha74] , where it is attributed to Erdős. First investigated by Rényi and Rédei [Re47] . Erdős [Er49b] proved that $f(k)<k^{1-c}$ for some $c>0$. The conjecture that $f(k)\to \infty$ is due to Erdős and Rényi. This was solved by Schinzel [Sc87] , who proved that\[f(k) > \frac{\log\log k}{\log 2}.\]In fact Schinzel proves lower bounds for the corresponding problem with $P(x)^n$ for any integer $n\geq 1$, where the coefficients of the polynomial can be from any field with zero or sufficiently large positive characteristic. Schinzel and Zannier [ScZa09] have improved this to\[f(k) \gg \log k.\] Additional thanks to : Stefan Steinerberger Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 08 April 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #485, https://www.erdosproblems.com/485, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos485

/-- The number of nonzero terms of a rational polynomial, represented by the
cardinality of its coefficient support. -/
def termCount (P : Polynomial ℚ) : ℕ :=
  P.support.card

/-- The set of possible numbers of terms in the square of a polynomial having
exactly `k` nonzero terms. -/
def values (k : ℕ) : Set ℕ :=
  {n | ∃ P : Polynomial ℚ, termCount P = k ∧ termCount (P ^ 2) = n}

/-- The extremal quantity from the source: the minimum number of terms in
`P(x)^2` among rational polynomials with exactly `k` nonzero terms.  This uses
`Nat.sInf`; the bounded-below and nonemptiness facts are recorded separately so
that the default value for an empty set is not being used. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf (values k)

/-- The defining set is nonempty for every number of terms.  The omitted
construction is the elementary choice of a polynomial with prescribed finite
support. -/
theorem values_nonempty (k : ℕ) : (values k).Nonempty := by
  sorry

/-- The defining set is bounded below by zero, so the `sInf` in `f` is not
using an accidental lower-bound convention. -/
theorem values_bddBelow (k : ℕ) : BddBelow (values k) := by
  refine ⟨0, ?_⟩
  intro n hn
  exact Nat.zero_le n

/-- A proved sanity control: the zero polynomial has zero terms, and its
square also has zero terms. -/
theorem zero_square_control :
    termCount ((0 : Polynomial ℚ) ^ 2) = 0 := by
  simp [termCount]

/-- A second sanity control showing that the defining set at zero contains
the expected value zero. -/
theorem zero_mem_values : 0 ∈ values 0 := by
  refine ⟨0, ?_, ?_⟩
  · simp [termCount]
  · simp [termCount]

/-- The question asks whether the extremal function tends to infinity, written
as the usual eventual lower-bound formulation over the natural numbers. -/
def question : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → M ≤ f k

/-- Schinzel's recorded lower bound, formalized with the literal
`log log k / log 2` expression for the range `k ≥ 4`. -/
def SchinzelLowerBound : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    Real.log (Real.log (k : ℝ)) / Real.log 2 < (f k : ℝ)

/-- The source records Schinzel's theorem as the resolution of the problem.
The proof of this literature result is not reproduced here. -/
theorem schinzel_lower_bound : SchinzelLowerBound := by
  sorry

/-- Schinzel's lower bound implies the asserted divergence of `f`.  The
analytic passage from the displayed logarithmic bound to divergence is left
as an explicit proof gap. -/
theorem schinzel_implies_question :
    SchinzelLowerBound → question := by
  sorry

/-- The resolved answer to the source question.  This consumes the named
Schinzel result rather than presenting the original conjecture as an
unqualified theorem. -/
theorem answer : question := by
  exact schinzel_implies_question schinzel_lower_bound

#print axioms zero_square_control

end Erdos485
