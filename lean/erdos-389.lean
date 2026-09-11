import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Erdős Problem #389.

For natural numbers n and k, the first product is
  n (n + 1) ... (n + k - 1),
and the shifted product is
  (n + k) (n + k + 1) ... (n + 2k - 1).
The condition 1 ≤ k records that the displayed products are nonempty.
-/

def intervalProduct (n k : ℕ) : ℕ :=
  Finset.prod (Finset.range k) (fun i => n + i)

def dividesShifted (n k : ℕ) : Prop :=
  intervalProduct n k ∣ intervalProduct (n + k) k

def admissible (n k : ℕ) : Prop :=
  1 ≤ k ∧ dividesShifted n k

def erdos389 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, admissible n k

theorem witness_pos : admissible 3 4 := by
  norm_num [admissible, dividesShifted, intervalProduct, Finset.prod_range_succ]

theorem witness_neg : ¬ admissible 2 1 := by
  norm_num [admissible, dividesShifted, intervalProduct, Finset.prod_range_succ]

theorem example_two_five : dividesShifted 2 5 := by
  norm_num [dividesShifted, intervalProduct, Finset.prod_range_succ]

theorem erdos_389_conjecture : erdos389 := by
  sorry

end