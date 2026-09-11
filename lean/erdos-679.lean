import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def omegaCount (n : ℕ) : ℕ :=
  if n = 0 then
    0
  else
    (Finset.filter
      (fun p : ℕ => Nat.Prime p ∧ p ∣ n)
      (Finset.range (n + 1))).card

def Good (ε : ℝ) (n K : ℕ) : Prop :=
  ∀ k : ℕ, K ≤ k → k < n →
    (omegaCount (n - k) : ℝ) <
      (1 + ε) * Real.log (k : ℝ) /
        Real.log (Real.log (k : ℝ))

def Original : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Set.Infinite {n : ℕ | ∃ K : ℕ, Good ε n K}

def StrongGood (C : ℝ) (n K : ℕ) : Prop :=
  ∀ k : ℕ, K ≤ k → k < n →
    (omegaCount (n - k) : ℝ) <
      Real.log (k : ℝ) /
        Real.log (Real.log (k : ℝ)) + C

def Stronger : Prop :=
  ∃ C : ℝ,
    Set.Infinite {n : ℕ | ∃ K : ℕ, StrongGood C n K}

theorem omega_two : omegaCount 2 = 1 := by
  decide

theorem witness_pos : Good (1 : ℝ) 1 1 := by
  intro k hk hkn
  exact (Nat.not_lt_of_ge hk hkn).elim

theorem witness_neg : ¬ Good (0 : ℝ) 3 1 := by
  intro h
  have hh := h 1 (by norm_num) (by norm_num)
  norm_num [Good, omega_two] at hh

theorem erdos_679_original : Original := by
  sorry

end
