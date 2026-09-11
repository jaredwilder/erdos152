import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
The source contains the numerical data
#969, [Er65b], [Er81h,p.176], [Wa63], [EvLi31], 1, 6, 2, 1/2,
x^(1/2), x^(1/2-o(1)), 1/4, 11/35, 16, 0, 2025, 19, 2026, 8, 30,
and OEIS A013928.
-/

def squarefreeNat (n : ℕ) : Prop :=
  n ≠ 0 ∧
    ∀ p ∈ Finset.Icc 2 n, Nat.Prime p → ¬ p ^ 2 ∣ n

def Q (x : ℕ) : ℕ :=
  (Finset.Icc 1 x).filter squarefreeNat |>.card

def errorTerm (x : ℕ) : ℝ :=
  (Q x : ℝ) - (6 / (Real.pi ^ 2)) * (x : ℝ)

def elementaryExponent : ℝ :=
  (1 : ℝ) / 2

def conjecturalExponent : ℝ :=
  (1 : ℝ) / 4

def conditionalExponent : ℝ :=
  (11 : ℝ) / 35

theorem witness_pos : squarefreeNat 1 := by
  unfold squarefreeNat
  constructor
  · norm_num
  · intro p hp hprime
    simp only [Finset.mem_Icc] at hp
    omega

theorem witness_neg : ¬ squarefreeNat 4 := by
  unfold squarefreeNat
  intro h
  rcases h with ⟨hzero, hall⟩
  have hpem : 2 ∈ Finset.Icc 2 4 := by
    norm_num
  have hprime : Nat.Prime 2 := by
    norm_num
  have hn := hall 2 hpem hprime
  norm_num at hn

theorem conjectured_order_of_magnitude :
    ∃ c C X : ℝ,
      0 < c ∧
      0 < C ∧
      0 < X ∧
      ∀ x : ℕ,
        X ≤ (x : ℝ) →
          c * Real.rpow (x : ℝ) ((1 : ℝ) / 4) ≤ |errorTerm x| ∧
            |errorTerm x| ≤ C * Real.rpow (x : ℝ) ((1 : ℝ) / 4) := by
  sorry

end