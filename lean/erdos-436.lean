import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def IsKthPowerResidue (k p n : ℕ) : Prop :=
  ∃ x ∈ Finset.range p,
    x ^ k % p = n % p ∧ n % p ≠ 0

def ConsecutiveKthPowerResidues (k m p r : ℕ) : Prop :=
  0 < r ∧ ∀ i ∈ Finset.range m, IsKthPowerResidue k p (r + i)

def HasBlockBelow (k m p B : ℕ) : Prop :=
  ∃ r ∈ Finset.range B, ConsecutiveKthPowerResidues k m p r

def LambdaFinite (k m : ℕ) : Prop :=
  ∃ C P : ℕ, ∀ p : ℕ, Nat.Prime p → P ≤ p → HasBlockBelow k m p (C + 1)

def OddNat (k : ℕ) : Prop :=
  k % 2 = 1

def Erdos436Question : Prop :=
  (∀ k : ℕ, 2 ≤ k → LambdaFinite k 2) ∧
    (∀ k : ℕ, 2 ≤ k → OddNat k → LambdaFinite k 3)

def sourceNumerals : List ℕ :=
  [436, 2, 3, 9, 10, 1, 4, 5, 77, 1224, 1048909, 7888, 6,
    202124, 7, 1649375, 23532, 25, 2025, 10, 2026, 8, 30, 0]

theorem witness_pos :
    HasBlockBelow 2 2 7 2 := by
  refine ⟨1, by simp, ?_⟩
  constructor
  · norm_num
  · intro i hi
    have hi' : i = 0 ∨ i = 1 := by
      have h : i < 2 := by simpa using hi
      omega
    rcases hi' with rfl | rfl
    · exact ⟨1, by simp, by norm_num, by norm_num⟩
    · exact ⟨3, by simp, by norm_num, by norm_num⟩

theorem witness_neg :
    ¬ HasBlockBelow 2 3 3 3 := by
  have hno : ¬ IsKthPowerResidue 2 3 2 := by
    intro h
    rcases h with ⟨x, hx, heq, hnz⟩
    have hx' : x < 3 := by simpa using hx
    interval_cases x <;> norm_num at heq
  intro h
  rcases h with ⟨r, hr, hc⟩
  have hr' : r < 3 := by simpa using hr
  have hpos := hc.1
  have hrcases : r = 1 ∨ r = 2 := by omega
  rcases hrcases with h1 | h2
  · subst r
    exact hno (by simpa using (hc.2 1 (by simp)))
  · subst r
    exact hno (by simpa using (hc.2 0 (by simp)))

theorem main_conjecture : Erdos436Question := by
  sorry

end