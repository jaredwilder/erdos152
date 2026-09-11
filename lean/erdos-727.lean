import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def DividesAt (k n : ℕ) : Prop :=
  (Nat.factorial (n + k)) ^ 2 ∣ Nat.factorial (2 * n)

theorem witness_pos : DividesAt 0 0 := by
  norm_num [DividesAt]

theorem witness_neg : ¬ DividesAt 2 0 := by
  norm_num [DividesAt]

theorem erdos_727 :
    ∀ k : ℕ, 2 ≤ k →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ DividesAt k n := by
  sorry

end