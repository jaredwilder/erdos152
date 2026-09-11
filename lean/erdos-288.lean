import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-
Erdős problem 288.  An interval is represented by its positive integral
endpoints, and its reciprocal sum is taken over the corresponding `Finset.Icc`.
-/

def intervalSum (a b : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc a b, (1 : ℚ) / (n : ℚ)

def IsGood (p : (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  0 < p.1.1 ∧
    p.1.1 ≤ p.1.2 ∧
    0 < p.2.1 ∧
    p.2.1 ≤ p.2.2 ∧
    0 ≤ intervalSum p.1.1 p.1.2 + intervalSum p.2.1 p.2.2 ∧
    (intervalSum p.1.1 p.1.2 + intervalSum p.2.1 p.2.2).den = 1

def erdos288 : Prop :=
  Set.Finite {p : (ℕ × ℕ) × (ℕ × ℕ) | IsGood p}

theorem source_example :
    (1 : ℚ) / 3 + 1 / 4 + 1 / 5 + 1 / 6 + 1 / 20 = 1 := by
  norm_num

theorem witness_pos : IsGood ((1, 1), (1, 1)) := by
  norm_num [IsGood, intervalSum]

theorem witness_neg : ¬ IsGood ((2, 2), (3, 3)) := by
  norm_num [IsGood, intervalSum]

theorem erdos_288 : erdos288 := by
  sorry

end