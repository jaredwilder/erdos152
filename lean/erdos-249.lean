import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

-- Erdős problem 249.
def IsIrrational (x : ℝ) : Prop := Irrational x

noncomputable def totientSeries : ℝ :=
  ∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n

theorem witness_pos : IsIrrational (Real.sqrt 2) := by
  change Irrational (Real.sqrt 2)
  exact irrational_sqrt_two

theorem witness_neg : ¬ IsIrrational (0 : ℝ) := by
  norm_num [IsIrrational, Irrational]

theorem erdos_problem_249 : IsIrrational totientSeries := by
  sorry

end
