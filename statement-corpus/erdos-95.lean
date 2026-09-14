/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $x_1,\ldots,x_n\in\mathbb{R}^2$ determine the set of distances $\{u_1,\ldots,u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of points. Then for all $\epsilon>0$\[\sum_i f(u_i)^2 \ll_\epsilon n^{3+\epsilon}.\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#95 : [Er92e] [Er95] [Er97c] [Er97f] geometry | convex | distances The case when the points determine a convex polygon was solved by Altman [Al63] . Note it is trivial that $\sum f(u_i)=\binom{n}{2}$. Solved by Guth and Katz [GuKa15] who proved the upper bound\[ \sum_i f(u_i)^2 \ll n^3\log n.\]See also [94] . Additional thanks to : JoshuaB Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 11 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #95, https://www.erdosproblems.com/95, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem95

/-- The Euclidean plane used for the distance problem. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- An unordered pair of distinct points, represented by its increasing ordered pair. -/
abbrev PointPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The finite set of distances determined by a configuration `x`.

The source says that `x₁, ..., xₙ ∈ ℝ²` determine a set of distances. -/
noncomputable def distanceSet (n : ℕ) (x : Fin n → Plane) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun p : PointPair n => dist (x p.1.1) (x p.1.2))

/-- The number of pairs in a configuration `x` whose distance is `u`. -/
noncomputable def distanceMultiplicity (n : ℕ) (x : Fin n → Plane) (u : ℝ) : ℕ :=
  Fintype.card {p : PointPair n // dist (x p.1.1) (x p.1.2) = u}

/-- The sum of the squares of the distance multiplicities, with the natural-number
multiplicities coerced to real numbers. -/
noncomputable def distanceSquareSum (n : ℕ) (x : Fin n → Plane) : ℝ :=
  ∑ u ∈ distanceSet n x, (distanceMultiplicity n x u : ℝ) ^ 2

/-- The literal formalization of the question.

The source clause says “for all `ε > 0`, the sum is bounded by a constant
depending on `ε` times `n^(3+ε)`”; this definition uses `Real.rpow` for the
real exponent and quantifies uniformly over every finite Euclidean
configuration. -/
def Erdos95Question : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∀ x : Fin n → Plane,
        distanceSquareSum n x ≤ C * Real.rpow (n : ℝ) (3 + ε)

/-- The resolved Guth–Katz bound recorded by the source.

The source's resolution says “`∑ f(u_i)^2 ≪ n^3 log n`”; here `≪` is
formalized as the existence of one positive absolute constant `C` valid for
all finite configurations. -/
def GuthKatzBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ x : Fin n → Plane,
      distanceSquareSum n x ≤ C * (n : ℝ) ^ 3 * Real.log (n : ℝ)

/-- The resolution node records that the question is solved by Guth and Katz. -/
def GuthKatzResolution : Prop :=
  GuthKatzBound

/-- A zero-point configuration determines no distances. -/
theorem distanceSet_zero (x : Fin 0 → Plane) :
    distanceSet 0 x = ∅ := by
  classical
  ext u
  simp [distanceSet, PointPair]

/-- Consequently, the distance-square sum vanishes for the zero-point configuration. -/
theorem distanceSquareSum_zero (x : Fin 0 → Plane) :
    distanceSquareSum 0 x = 0 := by
  rw [distanceSet_zero x]
  simp [distanceSquareSum]

#print axioms distanceSet_zero
#print axioms distanceSquareSum_zero

end ErdosProblem95