/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Given any $n$ distinct points in $\mathbb{R}^2$ let $f(n)$ count the number of distinct lines determined by these points. What are the possible values of $f(n)$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#606 : [Er85] geometry A question of Grünbaum. The Sylvester-Gallai theorem implies that if $f(m)>1$ then $f(m)\geq n$. Erdős showed that, for some constant $c>0$, all integers in $[cn^{3/2},\binom{n}{2}]$ are possible except $\binom{n}{2}-1$ and $\binom{n}{2}-3$. Solved (for all sufficiently large $n$) completely by Erdős and Salamon [ErSa88] ; the full description is too complicated to be given here. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #606, https://www.erdosproblems.com/606, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos606

/-- The affine line through two points of the Euclidean plane, represented as its
set of points.  This uses `EuclideanSpace`, rather than the sup-metric on a product. -/
def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ t : ℝ, x = p + t • (q - p)}

/-- The unordered pairs of indices represented by ordered pairs `i < j`. -/
def pairSet (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

/-- The number of distinct affine lines determined by the indexed points `p`.
The source's hypothesis that the points are distinct is represented separately
by `Function.Injective p`. -/
noncomputable def lineCount (n : ℕ)
    (p : Fin n → EuclideanSpace ℝ (Fin 2)) : ℕ :=
  ((pairSet n).image (fun ij => lineThrough (p ij.1) (p ij.2))).card

/-- The set of possible values of the number of determined lines for `n`
distinct points in the Euclidean plane. -/
noncomputable def possibleValues (n : ℕ) : Set ℕ :=
  {k | ∃ p : Fin n → EuclideanSpace ℝ (Fin 2),
    Function.Injective p ∧ lineCount n p = k}

/-- A proved small-case control: two indexed points determine exactly one
distinct line, independently of the particular locations of the points. -/
theorem lineCount_two_control
    (p : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    lineCount 2 p = 1 := by
  have hp :
      pairSet 2 = {((0 : Fin 2), (1 : Fin 2))} := by
    decide
  simp [lineCount, hp]

/-- The recorded Erdős lower-range result, formalized using the literal real
inequality `c * n^(3/2) ≤ k`.  The exact complete description mentioned in the
source is not reproduced here because the source explicitly says it is too
complicated to give; the theorem below records the stated eventual range result.
This declaration is an explicit literature-result gap, not a proved derivation. -/
theorem erdos_salamon_eventual_lower_range :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ,
        c * Real.rpow (n : ℝ) (3 / 2 : ℝ) ≤ (k : ℝ) →
        (k : ℝ) ≤ (Nat.choose n 2 : ℝ) →
        k ≠ Nat.choose n 2 - 1 →
        k ≠ Nat.choose n 2 - 3 →
        k ∈ possibleValues n := by
  sorry Erdos606
