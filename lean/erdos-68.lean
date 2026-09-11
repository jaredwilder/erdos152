import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
noncomputable def erdosSum : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) / ((Nat.factorial n : ℝ) - 1)
  else
    0

def IsIrrational (x : ℝ) : Prop :=
  Irrational x

theorem witness_pos : IsIrrational (Real.sqrt 2) := by
  simpa [IsIrrational] using irrational_sqrt_two

theorem witness_neg : ¬ IsIrrational (0 : ℝ) := by
  norm_num [IsIrrational, Irrational]

theorem erdos_problem_68 : IsIrrational erdosSum := by
  sorry

end
