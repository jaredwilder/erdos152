/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
For $A\subset \mathbb{R}^2$ we define the upper density as\[\overline{\delta}(A)=\limsup_{R\to \infty}\frac{\lambda(A \cap B_R)}{\lambda(B_R)},\]where $\lambda$ is the Lebesgue measure and $B_R$ is the ball of radius $R$. Estimate\[m_1=\sup \overline{\delta}(A),\]where $A$ ranges over all measurable subsets of $\mathbb{R}^2$ without two points distance $1$ apart. In particular, is $m_1\leq 1/4$?
-/

/- 
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#232 : [Er85,p.4] geometry | distances A question of Moser [Mo66] . A lower bound of $m_1\geq \pi/8\sqrt{3}\approx 0.2267$ is given by taking the union of open circular discs of radius $1/2$ at a regular hexagonal lattice suitably spaced apart. Croft [Cr67] gives a small improvement of $m_1\geq 0.22936$. The trivial upper bound is $m_1\leq 1/2$, since for any unit vector $u$ the sets $A$ and $A+u$ must be disjoint. Erdős' question was solved by Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki [ACMVZ23] who proved that $m_1\leq 0.247$. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 02 October 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #232, https://www.erdosproblems.com/232, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter
open MeasureTheory

-- @category research solved








open Classical Filter

namespace Erdos232

/-- The Euclidean plane, represented with its genuine Euclidean metric rather than a
    product sup metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A measurable subset of the plane with no two points at distance one. -/
def UnitDistanceFree (A : Set Plane) : Prop :=
  MeasurableSet A ∧
    ∀ ⦃x y : Plane⦄, x ∈ A → y ∈ A → dist x y ≠ 1

/-- The upper asymptotic density of a measurable subset of the Euclidean plane.
    The limsup is taken over real radii tending to infinity, and the measure is
    Lebesgue measure. -/
noncomputable def upperDensity (A : Set Plane) : ℝ≥0∞ :=
  limsup
    (fun R : ℝ =>
      volume (A ∩ Metric.ball (0 : Plane) R) /
        volume (Metric.ball (0 : Plane) R))
    atTop

/-- The set of upper densities of measurable unit-distance-free subsets of the plane. -/
noncomputable def densityValues : Set ℝ≥0∞ :=
  {d | ∃ A : Set Plane, UnitDistanceFree A ∧ d = upperDensity A}

/-- The supremum requested in the source, formalized in extended nonnegative reals. -/
noncomputable def m₁ : ℝ≥0∞ :=
  sSup densityValues

/-- The empty set is a measurable unit-distance-free subset of the plane. -/
theorem empty_is_unitDistanceFree :
    UnitDistanceFree (∅ : Set Plane) := by
  constructor
  · exact MeasurableSet.empty
  · intro x y hx hy
    exact False.elim (by simpa using hx)

/-- The upper density of the empty set is zero. This is a proved control showing that
    the density predicate is not vacuous or identically maximal. -/
theorem empty_upperDensity :
    upperDensity (∅ : Set Plane) = 0 := by
  simp [upperDensity]

/-- The set of admissible density values is nonempty, witnessed by the empty set. -/
theorem densityValues_nonempty :
    Set.Nonempty densityValues := by
  refine ⟨0, ∅, empty_is_unitDistanceFree, ?_⟩
  exact empty_upperDensity.symm

/-- The density values are bounded above by the top element of the codomain.
    This explicitly records boundedness needed when interpreting `sSup`; the
    codomain `ℝ≥0∞` has a top element. -/
theorem densityValues_bddAbove :
    BddAbove densityValues := by
  refine ⟨⊤, ?_⟩
  intro d hd
  exact le_top

/-- The recorded resolution of Erdős' problem: the work of Ambrus, Csiszárik,
    Matolcsi, Varga, and Zsámboki proves the upper bound `m₁ ≤ 0.247`.
    The proof of that external result remains an explicit formalization gap. -/
theorem m₁_upper_bound :
    m₁ ≤ (247 : ℝ≥0∞) / 1000 := by
  sorry

#print axioms empty_is_unitDistanceFree
#print axioms empty_upperDensity
#print axioms densityValues_nonempty
#print axioms densityValues_bddAbove

end Erdos232
