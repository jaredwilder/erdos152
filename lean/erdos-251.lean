import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def IsIrrational (x : ℝ) : Prop :=
  Irrational x

def primeNumber (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

def primePowerSeries : ℝ :=
  ∑' n : ℕ, (primeNumber (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

theorem witness_pos : IsIrrational (Real.sqrt 2) := by
  simpa [IsIrrational] using irrational_sqrt_two

theorem witness_neg : ¬ IsIrrational (0 : ℝ) := by
  norm_num [IsIrrational, Irrational]

theorem erdos_problem_251 : IsIrrational primePowerSeries := by
  sorry

end
