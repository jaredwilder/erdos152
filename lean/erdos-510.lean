import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def cosineLowerBound (c : ℝ) (A : Finset ℤ) (N : ℕ) : Prop :=
  (1 ≤ N ∧ A.card = N) →
    ∃ θ : ℝ,
      (Finset.sum A (fun n => Real.cos ((n : ℝ) * θ))) < -c * Real.sqrt (N : ℝ)

def erdosProblem510 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ N : ℕ, ∀ A : Finset ℤ, cosineLowerBound c A N

theorem witness_pos :
    cosineLowerBound (1 / 2 : ℝ) ({(1 : ℤ)} : Finset ℤ) 1 := by
  unfold cosineLowerBound
  intro h
  refine ⟨Real.pi, ?_⟩
  norm_num [Real.cos_pi]

theorem witness_neg :
    ¬ cosineLowerBound (1 : ℝ) ({(0 : ℤ)} : Finset ℤ) 1 := by
  intro h
  unfold cosineLowerBound at h
  obtain ⟨θ, hθ⟩ := h ⟨by norm_num, by simp⟩
  norm_num [Real.cos_zero] at hθ

theorem erdos_problem_510 : erdosProblem510 := by
  sorry

end