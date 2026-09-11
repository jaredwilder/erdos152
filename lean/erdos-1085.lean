import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Formalization of Erdős problem 1085.

The source concerns unit-distance pairs among finite sets of points in Euclidean
space.  The definition below uses finite sets of points with real coordinates.
-/

/- Source numerals: 1085, 2, 3, 1, 4, 3, 90, 84, 103, 75, 60, 67, 97, 09, 5, 40, 6. -/

abbrev Point (d : ℕ) := Fin d → ℝ

def squaredDistance {d : ℕ} (p q : Point d) : ℝ :=
  ∑ i, (p i - q i) ^ 2

def HasUnitDistance {d : ℕ} (p q : Point d) : Prop :=
  squaredDistance p q = 1

noncomputable def unitPairCount {d : ℕ} (s : Finset (Point d)) : ℕ := by
  classical
  exact
    ((s.product s).filter
      (fun pq => pq.1 ≠ pq.2 ∧ HasUnitDistance pq.1 pq.2)).card / 2

noncomputable def f (d n : ℕ) : ℕ :=
  sInf
    {k : ℕ |
      ∀ s : Finset (Point d), s.card = n → unitPairCount s ≤ k}

/-- The two points `(0, 0)` and `(1, 0)` are at unit distance. -/
theorem witness_pos :
    HasUnitDistance (d := 2) ![(0 : ℝ), 0] ![(1 : ℝ), 0] := by
  norm_num [HasUnitDistance, squaredDistance, Fin.sum_univ_succ]

/-- The two points `(0, 0)` and `(2, 0)` are not at unit distance. -/
theorem witness_neg :
    ¬ HasUnitDistance (d := 2) ![(0 : ℝ), 0] ![(2 : ℝ), 0] := by
  norm_num [HasUnitDistance, squaredDistance, Fin.sum_univ_succ]

/--
The estimate asked for in Erdős problem 1085, expressed using eventual
two-sided power bounds in the planar case.
-/
theorem erdos_problem_1085_estimate :
    ∃ c C : ℝ,
      0 < c ∧
        0 < C ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            (n : ℝ) ^ (1 + c) ≤ (f 2 n : ℝ) ∧
              (f 2 n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3) := by
  sorry

end