import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def HasLargePrime (k n : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ n

def Good (k n : ℕ) : Prop :=
  ∀ a : ℕ, k < a →
    ∃ i : ℕ, i < n ∧ HasLargePrime k (a + i)

noncomputable def f (k : ℕ) : ℕ :=
  if h : ∃ n : ℕ, Good k n then Nat.find h else 0

theorem witness_pos : Good 0 2 := by
  unfold Good HasLargePrime
  intro a ha
  have hmod : a % 2 = 0 ∨ a % 2 = 1 := by
    omega
  cases hmod with
  | inl h =>
      refine ⟨0, by omega, 2, by norm_num, by omega, ?_⟩
      exact Nat.dvd_of_mod_eq_zero h
  | inr h =>
      refine ⟨1, by omega, 2, by norm_num, by omega, ?_⟩
      use (a + 1) / 2
      omega

theorem witness_neg : ¬ Good 2 1 := by
  unfold Good HasLargePrime
  intro h
  obtain ⟨i, hi, p, hp, hpk, hpd⟩ := h 8 (by norm_num)
  have hi0 : i = 0 := by
    omega
  subst i
  have hp_le : p ≤ 8 := Nat.le_of_dvd (by norm_num) hpd
  interval_cases p <;> norm_num at hp <;> norm_num at hpk <;> norm_num at hpd

theorem polylog_estimate :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        (f k : ℝ) ≤ C * (3 * Real.log (k : ℝ)) ^ d := by
  sorry

end