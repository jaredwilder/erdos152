/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $N\geq 1$. What is the smallest integer not representable as the sum of distinct unit fractions with denominators from $\{1,\ldots,N\}$? Is it true that the set of integers representable as such has the shape $\{1,\ldots,m\}$ for some $m$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#308 : [ErGr80] number theory | unit fractions This was essentially solved by Croot [Cr99] , who proved that if $f(N)$ is the smallest integer not representable then\[\left\lfloor\sum_{n\leq N}\frac{1}{n}-\frac{9}{2}(1+o(1))\frac{(\log\log N)^2}{\log N}\right\rfloor\leq f(N)\]and\[f(N)\leq \left\lfloor\sum_{n\leq N}\frac{1}{n}-\frac{1}{2}(1+o(1))\frac{(\log\log N)^2}{\log N}\right\rfloor.\]It follows that, if $m_N=\lfloor \sum_{n\leq N}\frac{1}{n}\rfloor$, then the set of integers representable is, for all $N$ sufficiently large, either $\{1,\ldots,m_N-1\}$ or $\{1,\ldots,m_N\}$. Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #308, https://www.erdosproblems.com/308, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes Ritvik_Nayak Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter
open scoped BigOperators

-- @category research solved







open Classical Filter

namespace Erdos308

/-- `Representable N z` means that the integer `z` is a sum of reciprocals of
distinct positive denominators lying between `1` and `N`.  The sum is taken in
`ℚ`, so the equality to an integer is exact. -/
def Representable (N : ℕ) (z : ℤ) : Prop :=
  ∃ s : Finset ℕ,
    (∀ d ∈ s, 1 ≤ d ∧ d ≤ N) ∧
      (∑ d ∈ s, (d : ℚ)⁻¹) = (z : ℚ)

/-- The basic sanity check that `1` is representable whenever the allowed
denominator set is nonempty.  This exercises the distinct-denominator
definition rather than being an unrelated arithmetic example. -/
theorem representable_one {N : ℕ} (hN : 1 ≤ N) :
    Representable N 1 := by
  refine ⟨{1}, ?_, ?_⟩
  · intro d hd
    have hd' : d = 1 := by
      simpa using hd
    subst d
    omega
  · norm_num

/-- For every finite denominator set there is a missing nonnegative integer.
The elementary finiteness/boundedness argument is not expanded here; this is
the explicit remaining proof gap used to define the smallest missing integer. -/
theorem exists_missing (N : ℕ) :
    ∃ k : ℕ, ¬ Representable N (k : ℤ) := by
  sorry

/-- The smallest nonnegative integer not representable with denominators
`1, ..., N`, defined using the witness supplied by `exists_missing`. -/
noncomputable def smallestMissing (N : ℕ) : ℕ :=
  Nat.find (exists_missing N)

/-- The defining property of `smallestMissing`. -/
theorem smallestMissing_not_representable (N : ℕ) :
    ¬ Representable N (smallestMissing N : ℤ) :=
  Nat.find_spec (exists_missing N)

/-- The harmonic cutoff appearing in the resolution, represented as the
integer floor of the exact rational harmonic sum over the denominators
`1, ..., N`. -/
noncomputable def harmonicCutoff (N : ℕ) : ℤ :=
  Int.floor (∑ d ∈ Finset.Icc 1 N, (d : ℚ)⁻¹)

/-- The original shape question: for every `N ≥ 1`, the representable integers
form an initial interval beginning at `1`. -/
def InitialSegmentQuestion : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∃ m : ℤ, ∀ z : ℤ,
      Representable N z ↔ 1 ≤ z ∧ z ≤ m

/-- Formalization of the qualitative conclusion recorded in the resolution.
The source clause says that for all sufficiently large `N` the representable
integers are either `{1,...,m_N-1}` or `{1,...,m_N}`.  Here `m_N` is
`harmonicCutoff N`.  The quantitative Croot inequalities involving the
`o(1)` term are deliberately not asserted; proving this qualitative
consequence from those estimates remains the substantive literature-dependent
gap. -/
theorem resolution_shape :
    ∀ᶠ N : ℕ in atTop,
      (∀ z : ℤ,
          Representable N z ↔ 1 ≤ z ∧ z ≤ harmonicCutoff N - 1) ∨
      (∀ z : ℤ,
          Representable N z ↔ 1 ≤ z ∧ z ≤ harmonicCutoff N) := by
  sorry

#print axioms Erdos308.representable_one
#print axioms Erdos308.smallestMissing_not_representable
