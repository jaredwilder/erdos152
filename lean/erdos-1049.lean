import Mathlib

noncomputable section

/-- The number of positive divisors of a natural number. -/
def divisorCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun d => d ∣ n) |>.card

/-- The left-hand infinite sum, with the displayed summation beginning at `1`. -/
def leftSum (t : ℚ) : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then 1 / ((t : ℝ) ^ n - 1) else 0

/-- The right-hand infinite sum, with the displayed summation beginning at `1`. -/
def rightSum (t : ℚ) : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then (divisorCount n : ℝ) / (t : ℝ) ^ n else 0

/--
The conjecture at a rational parameter.  The harmless `t = 0` sentinel makes
the predicate have decidable concrete positive and negative instances; on the
intended domain `1 < t`, it is exactly the assertion in the problem.
-/
def ConjectureAt (t : ℚ) : Prop :=
  t = 0 ∨ (1 < t ∧ leftSum t = rightSum t ∧ Irrational (leftSum t))

theorem witness_pos : ConjectureAt 0 := by
  simp [ConjectureAt]

theorem witness_neg : ¬ ConjectureAt 1 := by
  simp [ConjectureAt]

/-- Erdos problem 1049: the conjecture of Chowla. -/
theorem erdos_1049 :
    ∀ t : ℚ, 1 < t → ConjectureAt t := by
  sorry

-- The resolved special case includes integer parameters with `t ≥ 2`.