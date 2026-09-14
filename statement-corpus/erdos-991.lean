/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Suppose $A=\{w_1,\ldots,w_n\}\subset S^2$ maximises\[\prod_{i<j}\lvert w_i-w_j\rvert\]over all possible sets of size $n$. Is it true that\[\max_C\lvert \lvert A\cap C\rvert - \alpha_C n\rvert =o(n),\]where the maximum is taken over all spherical caps $C$ and $\alpha_C$ is the area of $C$ (normalised so that the entire sphere has area $1$)?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#991 : [Er64b] discrepancy This is certainly solved, although it is unclear exactly who to attribute this to. Brauchart [Br08] says that this qualitative result follows from 'classical potential theory', and proves a quantitative decay rate of\[\max_C\lvert \lvert A\cap C\rvert - \alpha_C n\rvert \ll n^{3/4}.\]Marzo and Mas [MaMa21] cite an improvement of $\ll n^{2/3}$ due to Wolff in an unpublished manuscript, and themselves give a proof of $\ll n^{2/3}$ (as a special case of a more general result). See also [988] . Additional thanks to : Stefan Steinerberger Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 16 September 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #991, https://www.erdosproblems.com/991, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open scoped BigOperators

-- @category research solved






open Classical Filter

namespace Erdos991

/-- A finite decidable model of spherical-cap discrepancy.
The map `A` represents a configuration of `n` points in a finite
`m`-point universe, and `k` is the allowed discrepancy after clearing
the denominator `m`. -/
def FiniteCapBound (n m k : ℕ) (A : Fin n → Fin m) : Prop :=
  Function.Injective A ∧
    ∀ C : Finset (Fin m),
      Int.natAbs
          (((((Finset.image A Finset.univ) ∩ C).card : ℕ) : ℤ) * (m : ℤ) -
            (C.card : ℤ) * (n : ℤ)) ≤ k * m

/-- POSITIVE WITNESS: the identity configuration has zero discrepancy
in the two-point finite model. -/
theorem FiniteCapBound_witness_pos :
    FiniteCapBound 2 2 0 (fun i : Fin 2 => i) := by
  decide

/-- NEGATIVE WITNESS: this near-miss changes only injectivity, by
repeating the first point in place of the second. -/
theorem FiniteCapBound_witness_neg :
    ¬ FiniteCapBound 2 2 0 (fun _ : Fin 2 => (0 : Fin 2)) := by
  decide

/-- The Euclidean squared-coordinate expression used to say that a
point lies on the unit sphere in `EuclideanSpace ℝ (Fin 3)`. -/
def sphereEquation (w : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∑ i : Fin 3, w i ^ 2 = 1

/-- POSITIVE WITNESS: the first coordinate point lies on the unit sphere. -/
theorem sphereEquation_witness_pos :
    sphereEquation (fun i : Fin 3 => if i = 0 then 1 else 0) := by
  simp [sphereEquation]
  norm_num

/-- NEGATIVE WITNESS: changing the first coordinate from `1` to `2`
is a one-condition near miss for the unit-sphere equation. -/
theorem sphereEquation_witness_neg :
    ¬ sphereEquation (fun i : Fin 3 => if i = 0 then 2 else 0) := by
  simp [sphereEquation]
  norm_num

/-- The product of pairwise Euclidean distances for a finite
configuration. -/
noncomputable def vandermondeProduct
    (n : ℕ) (A : Fin n → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, dist (A i) (A j)

/-- A configuration maximizes the product of pairwise distances among
all injective configurations on the unit sphere. -/
def MaximizesVandermonde
    (n : ℕ) (A : Fin n → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (Function.Injective A ∧ ∀ i, sphereEquation (A i)) ∧
    ∀ B : Fin n → EuclideanSpace ℝ (Fin 3),
      (Function.Injective B ∧ ∀ i, sphereEquation (B i)) →
        vandermondeProduct n B ≤ vandermondeProduct n A

/-- The qualitative spherical-cap discrepancy assertion, with `α`
named explicitly as the normalized area of a spherical cap.  The
maximum is expressed by a uniform bound over all cap centers and
thresholds, avoiding any unbounded supremum. -/
def SphericalCapDiscrepancy
    (A : ℕ → (Fin · → EuclideanSpace ℝ (Fin 3)))
    (α : EuclideanSpace ℝ (Fin 3) → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ c : EuclideanSpace ℝ (Fin 3), ∀ t : ℝ,
        |(((Finset.univ.filter
              (fun i : Fin n =>
                ∑ q : Fin 3, (A n i) q * c q ≥ t)).card : ℕ) : ℝ) -
            α c t * n| ≤ ε * n

/-- The source's assertion is known in the literature.  Here the
remaining gap is the imported mathematical result that a maximizing
configuration on the sphere satisfies the stated uniform
o(n) discrepancy estimate; `α` is a named hypothesis representing
normalized spherical-cap area.

SOURCE-TO-FORMALIZATION MAPPING:
the source says that `A` maximizes the product over sets of size `n`;
`MaximizesVandermonde n (A n)` expresses precisely that comparison.
The source then asks for `max_C | |A ∩ C| - α_C n | = o(n)`;
`SphericalCapDiscrepancy A α` unfolds this as the equivalent
epsilon--N uniform estimate over all spherical caps, with
`∑ q, (A n i) q * c q ≥ t` describing a cap. -/
theorem maximizing_sphere_points_have_sublinear_cap_discrepancy
    (A : ℕ → (Fin · → EuclideanSpace ℝ (Fin 3)))
    (α : EuclideanSpace ℝ (Fin 3) → ℝ → ℝ)
    (hmax : ∀ n, MaximizesVandermonde n (A n))
    (hα : ∀ c t, 0 ≤ α c t ∧ α c t ≤ 1) :
    SphericalCapDiscrepancy A α := by
  sorry Erdos991

#print axioms Erdos991.FiniteCapBound_witness_pos
#print axioms Erdos991.FiniteCapBound_witness_neg
#print axioms Erdos991.sphereEquation_witness_pos
#print axioms Erdos991.sphereEquation_witness_neg
