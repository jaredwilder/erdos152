import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def target : ℕ := 105

def targetFactors : Finset ℕ := {3, 5, 7}

def IsGood (n : ℕ) : Prop :=
  Nat.Coprime (Nat.choose (2 * n) n) target

theorem target_factorization : 3 * 5 * 7 = target := by
  norm_num [target]

theorem witness_pos : IsGood 0 := by
  norm_num [IsGood, target, Nat.choose, Nat.Coprime]

theorem witness_neg : ¬ IsGood 3 := by
  norm_num [IsGood, target, Nat.choose, Nat.Coprime]

theorem erdos_problem_376 :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ IsGood n := by
  sorry

end