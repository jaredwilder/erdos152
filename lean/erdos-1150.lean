import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def SignPattern (n : ℕ) (a : Fin (n + 1) → ℤ) : Prop :=
  ∀ i, a i = 1 ∨ a i = -1

def CoefficientsOf (P : Polynomial ℂ) (n : ℕ)
    (a : Fin (n + 1) → ℤ) : Prop :=
  ∀ i : Fin (n + 1), P.coeff (i : ℕ) = (a i : ℂ)

def CircleMaximum (P : Polynomial ℂ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ y = ‖P.eval z‖}

def Erdos1150 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a : Fin (n + 1) → ℤ, SignPattern n a →
        ∀ P : Polynomial ℂ,
          P.natDegree = n →
          CoefficientsOf P n a →
            (1 + c) * Real.sqrt (n : ℝ) < CircleMaximum P

theorem witness_pos :
    SignPattern 0 (fun _ : Fin (0 + 1) => (1 : ℤ)) := by
  simp [SignPattern]

theorem witness_neg :
    ¬ SignPattern 0 (fun _ : Fin (0 + 1) => (0 : ℤ)) := by
  simp [SignPattern]

theorem erdos_1150 : Erdos1150 := by
  sorry

end