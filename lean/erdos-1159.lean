import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def incidence (r : Fin n → Fin n → Bool) (p : Fin n) (l : Fin n) : Prop :=
  r p l = true

def pointCount {n : ℕ} (r : Fin n → Fin n → Bool)
    (S : Fin n → Bool) (l : Fin n) : ℕ :=
  (Finset.univ.filter (fun p => S p = true ∧ r p l = true)).card

def boundedBlockingSet {n : ℕ} (r : Fin n → Fin n → Bool) (C : ℕ) : Prop :=
  ∃ S : Fin n → Bool, ∀ l : Fin n,
    1 ≤ pointCount r S l ∧ pointCount r S l ≤ C

structure FiniteProjectivePlane (q : ℕ) where
  incidence : Fin (q * q + q + 1) → Fin (q * q + q + 1) → Bool
  order_nontrivial : 2 ≤ q
  line_card :
    ∀ l : Fin (q * q + q + 1),
      (Finset.univ.filter (fun p => incidence p l = true)).card = q + 1
  point_card :
    ∀ p : Fin (q * q + q + 1),
      (Finset.univ.filter (fun l => incidence p l = true)).card = q + 1
  two_points_unique_line :
    ∀ p₁ p₂ : Fin (q * q + q + 1), p₁ ≠ p₂ →
      ∃! l : Fin (q * q + q + 1),
        incidence p₁ l = true ∧ incidence p₂ l = true
  two_lines_unique_point :
    ∀ l₁ l₂ : Fin (q * q + q + 1), l₁ ≠ l₂ →
      ∃! p : Fin (q * q + q + 1),
        incidence p l₁ = true ∧ incidence p l₂ = true

def Erdos1159 : Prop :=
  ∃ C : ℕ, 1 < C ∧
    ∀ q : ℕ, ∀ P : FiniteProjectivePlane q,
      boundedBlockingSet P.incidence C

theorem witness_pos :
    boundedBlockingSet (n := 1) (fun _ _ => true) 2 := by
  refine ⟨fun _ => true, ?_⟩
  intro l
  fin_cases l
  norm_num [pointCount]

theorem witness_neg :
    ¬ boundedBlockingSet (n := 2) (fun _ _ => false) 2 := by
  intro h
  rcases h with ⟨S, hS⟩
  have h' := hS (0 : Fin 2)
  simp [pointCount] at h'

theorem erdos_1159 : Erdos1159 := by
  sorry

end