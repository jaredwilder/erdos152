/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Given any $n$ points in $\mathbb{R}^2$ when can one give positive weights to the points such that the sum of the weights of the points along every line containing at least two points is the same?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#735 : [Er81] geometry A problem of Murty, who conjectured this is only possible in one of four cases: all points on a line, no three points on a line, $n-1$ on a line, and a triangle, the angle bisectors, and the incentre (or a projective equivalence). The previous configurations are the only examples, as proved by Ackerman, Buchin, Knauer, Pinchasi, and Rote [ABKPR08] . Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #735, https://www.erdosproblems.com/735, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos735

/-- The Euclidean plane, represented with the Euclidean rather than product metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The affine line with base point `p` and nonzero direction `v`. -/
def OnAffineLine (p v x : Plane) : Prop :=
  ∃ t : ℝ, x = p + t • v

/-- Collinearity of three points on a genuine affine line. -/
def CollinearThree (a b c : Plane) : Prop :=
  ∃ p v : Plane, v ≠ 0 ∧ OnAffineLine p v a ∧
    OnAffineLine p v b ∧ OnAffineLine p v c

/-- A finite point configuration has no repeated points. -/
def PairwiseDistinct {n : ℕ} (P : Fin n → Plane) : Prop :=
  Function.Injective P

/-- The points of `P` lying on the affine line with base point `p` and direction `v`. -/
def PointsOnLine {n : ℕ} (P : Fin n → Plane) (p v : Plane) : Finset (Fin n) :=
  Finset.univ.filter (fun i => OnAffineLine p v (P i))

/-- The sum of the weights of the points of `P` lying on a specified affine line. -/
def LineWeight {n : ℕ} (P : Fin n → Plane) (w : Fin n → ℝ)
    (p v : Plane) : ℝ :=
  ∑ i ∈ Finset.univ, if OnAffineLine p v (P i) then w i else 0

/-- Positive weights whose line sums are constant on every line containing at least
two points. -/
def HasEqualLineSums {n : ℕ} (P : Fin n → Plane) : Prop :=
  ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
    ∃ c : ℝ, ∀ p v : Plane, v ≠ 0 →
      2 ≤ (PointsOnLine P p v).card →
      LineWeight P w p v = c

/-- All points lie on one affine line. -/
def AllPointsOnLine {n : ℕ} (P : Fin n → Plane) : Prop :=
  ∃ p v : Plane, v ≠ 0 ∧ ∀ i, OnAffineLine p v (P i)

/-- No three distinct points are collinear. -/
def NoThreeCollinear {n : ℕ} (P : Fin n → Plane) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ¬ CollinearThree (P i) (P j) (P k)

/-- Exactly `n - 1` points lie on some genuine affine line. -/
def AllButOneOnLine {n : ℕ} (P : Fin n → Plane) : Prop :=
  ∃ p v : Plane, v ≠ 0 ∧ (PointsOnLine P p v).card = n - 1

/-- The normalization of a nonzero vector, expressed using scalar multiplication. -/
def UnitVector (x : Plane) : Plane :=
  ‖x‖⁻¹ • x

/-- Two vectors are parallel. -/
def ParallelVectors (x y : Plane) : Prop :=
  ∃ r : ℝ, x = r • y

/-- A point lies on the internal angle bisector at vertex `a` of triangle `abc`.
The nonzero hypotheses ensure that the displayed unit directions are defined
geometrically. -/
def OnInternalBisector (a b c q : Plane) : Prop :=
  b ≠ a ∧ c ≠ a ∧ q ≠ a ∧
    ParallelVectors (q - a)
      (UnitVector (b - a) + UnitVector (c - a))

/-- A concrete, inspectable encoding of the exceptional triangle/bisector/incentre
configuration: the configuration consists exactly of the three triangle vertices
and a point lying on all three internal angle bisectors. -/
def TriangleBisectorsIncenter {n : ℕ} (P : Fin n → Plane) : Prop :=
  ∃ a b c q : Plane,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    OnInternalBisector a b c q ∧
    OnInternalBisector b a c q ∧
    OnInternalBisector c a b q ∧
    (∀ i, P i = a ∨ P i = b ∨ P i = c ∨ P i = q) ∧
    (∃ i, P i = a) ∧ (∃ i, P i = b) ∧
    (∃ i, P i = c) ∧ (∃ i, P i = q)

/-- The four cases in the resolution of Murty's problem, with the fourth case
given the explicit triangle, internal-angle-bisector, and incentre encoding above. -/
def MurtyCases {n : ℕ} (P : Fin n → Plane) : Prop :=
  AllPointsOnLine P ∨
  NoThreeCollinear P ∨
  AllButOneOnLine P ∨
  TriangleBisectorsIncenter P

/-- For the empty configuration, the equal-line-sums predicate is satisfied
vacuously by the unique empty weight function.  This is a proved control showing
that the formalized predicate has the expected degenerate behaviour. -/
theorem empty_hasEqualLineSums :
    HasEqualLineSums (fun i : Fin 0 => (Fin.elim0 i : Plane)) := by
  classical
  refine ⟨fun i => Fin.elim0 i, ?_, 0, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro p v hv hcard
    exfalso
    have hzero :
        (PointsOnLine (fun i : Fin 0 => (Fin.elim0 i : Plane)) p v).card = 0 := by
      simp [PointsOnLine]
    rw [hzero] at hcard
    omega

/-- The resolved classification theorem corresponding to the source sentence:
the source says that the previous configurations are the only examples, so the
formalized direction is from positive equal line sums to one of the four cases.
The source's phrase “in $\mathbb{R}^2$” is represented by `Plane`, namely
`EuclideanSpace ℝ (Fin 2)`.  The substantial classification argument is the
literature result cited in the resolution and remains an explicit proof gap here. -/
theorem murty_classification {n : ℕ} (P : Fin n → Plane)
    (hdistinct : PairwiseDistinct P) :
    HasEqualLineSums P → MurtyCases P := by
  sorry

#print axioms empty_hasEqualLineSums

end Erdos735
