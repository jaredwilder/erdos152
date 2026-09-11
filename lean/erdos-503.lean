import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def distSq {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ i, (x i - y i) ^ 2

def IsoscelesSet (d : ℕ) (A : Finset (Fin d → ℝ)) : Prop :=
  ∀ x ∈ (A : Set (Fin d → ℝ)),
    ∀ y ∈ (A : Set (Fin d → ℝ)),
      ∀ z ∈ (A : Set (Fin d → ℝ)),
        x ≠ y ∧ y ≠ z ∧ x ≠ z →
          distSq x y = distSq y z ∨
            distSq y z = distSq x z ∨
              distSq x z = distSq x y

def HasConfig (d n : ℕ) : Prop :=
  ∃ A : Finset (Fin d → ℝ), A.card = n ∧ IsoscelesSet d A

theorem witness_pos :
    IsoscelesSet 1 ({![0], ![1]} : Finset (Fin 1 → ℝ)) := by
  classical
  simp [IsoscelesSet]

theorem witness_neg :
    ¬ IsoscelesSet 1 ({![0], ![1], ![3]} : Finset (Fin 1 → ℝ)) := by
  classical
  intro h
  have hh :=
    h ![0] (by simp) ![1] (by simp) ![3] (by simp)
  norm_num [distSq, Fin.sum_univ_succ] at hh

/-
  The source records the exact answers 6 in dimension 2 and 8 in
  dimension 3, together with the general upper bound
  binomial(d + 2, 2), and the lower bound
  binomial(d + 1, 2) + 1.
-/
theorem erdos_problem_503 :
    HasConfig 2 6 ∧
      (∀ A : Finset (Fin 2 → ℝ), IsoscelesSet 2 A → A.card ≤ 6) ∧
      HasConfig 3 8 ∧
      (∀ A : Finset (Fin 3 → ℝ), IsoscelesSet 3 A → A.card ≤ 8) ∧
      (∀ d : ℕ, HasConfig d (Nat.choose (d + 1) 2 + 1)) ∧
      (∀ d : ℕ, ∀ A : Finset (Fin d → ℝ),
        IsoscelesSet d A → A.card ≤ Nat.choose (d + 2) 2) := by
  sorry

end
