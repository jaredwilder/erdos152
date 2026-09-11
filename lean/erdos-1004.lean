import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def TotientWindow (n K : ℕ) : Prop :=
  ∀ k₁ ∈ Finset.Icc 1 K, ∀ k₂ ∈ Finset.Icc 1 K,
    k₁ ≠ k₂ → Nat.totient (n + k₁) ≠ Nat.totient (n + k₂)

def GoodWindow (x n K : ℕ) : Prop :=
  n ≤ x ∧ TotientWindow n K

noncomputable def logarithmicWindow (x : ℕ) (c : ℝ) : ℕ :=
  ⌊Real.rpow (Real.log (x : ℝ)) c⌋₊

noncomputable def EPSBound (n : ℕ) (a : ℝ) : ℝ :=
  (n : ℝ) / Real.exp
    (a * Real.rpow (Real.log (n : ℝ)) (1 / (3 : ℝ)))

noncomputable def ErdosProblem1004 : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      ∃ n : ℕ, GoodWindow x n (logarithmicWindow x c)

theorem witness_pos : GoodWindow 0 0 1 := by
  unfold GoodWindow TotientWindow
  constructor
  · omega
  · intro k₁ hk₁ k₂ hk₂ hne
    have hk₁' : k₁ = 1 := by
      simp only [Finset.mem_Icc] at hk₁
      omega
    have hk₂' : k₂ = 1 := by
      simp only [Finset.mem_Icc] at hk₂
      omega
    exact (hne (by omega)).elim

theorem witness_neg : ¬ GoodWindow 0 0 2 := by
  intro h
  unfold GoodWindow TotientWindow at h
  rcases h with ⟨_, htw⟩
  have h' := htw 1 (by simp) 2 (by simp) (by omega)
  norm_num at h'

theorem erdos_problem_1004 : ErdosProblem1004 := by
  sorry

end