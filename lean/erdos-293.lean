import Mathlib

noncomputable section
open scoped BigOperators
open scoped Classical
open BigOperators

def u : ℕ → ℕ
  | 0 => 1
  | n + 1 => u n * (u n + 1)

def solutionBound (k : ℕ) : ℕ :=
  k * u k

def IsUnitFractionSolution (k : ℕ)
    (x : Fin k → Fin (solutionBound k + 1)) : Prop :=
  (∀ i, 1 ≤ (x i).val) ∧
    (∀ ⦃i j⦄, i < j → (x i).val < (x j).val) ∧
      (∑ i, (1 : ℚ) / ((x i).val : ℚ)) = 1

def Appears (k m : ℕ) : Prop :=
  ∃ x : Fin k → Fin (solutionBound k + 1),
    IsUnitFractionSolution k x ∧
      ∃ i, (x i).val = m

instance (k m : ℕ) : Decidable (Appears k m) := by
  unfold Appears IsUnitFractionSolution
  infer_instance

def missingWitness (k : ℕ) : ∃ m, ¬ Appears k m := by
  refine ⟨solutionBound k + 1, ?_⟩
  intro h
  rcases h with ⟨x, hx, i, hi⟩
  have hlt : (x i).val < solutionBound k + 1 := (x i).isLt
  omega

def v (k : ℕ) : ℕ :=
  Nat.find (missingWitness k)

theorem witness_pos : Appears 1 1 := by
  let x : Fin 1 → Fin (solutionBound 1 + 1) :=
    fun _ => ⟨1, by norm_num [solutionBound, u]⟩
  refine ⟨x, ?_, ?_⟩
  · unfold IsUnitFractionSolution
    constructor
    · intro i
      simp [x]
    constructor
    · intro i j hij
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      omega
    · simp [x, Fin.sum_univ_succ]
  · refine ⟨0, ?_⟩
    simp [x]

theorem witness_neg : ¬ Appears 1 2 := by
  intro h
  rcases h with ⟨x, hx, i, hi⟩
  have hi0 : i = 0 := Fin.eq_zero i
  subst i
  have hsum := hx.2.2
  norm_num [Fin.sum_univ_succ, hi] at hsum

theorem growth_estimate :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        Real.exp (c * (k : ℝ) ^ 2) ≤ (v k : ℝ) := by
  sorry

end