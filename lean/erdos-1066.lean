import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
structure FiniteGraph (n : ℕ) where
  edge : Fin n → Fin n → Bool

def Independent {n : ℕ} (G : FiniteGraph n) (s : Finset (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ∈ s → j ∈ s → i ≠ j → G.edge i j = false

def HasIndependentSetAtLeast {n : ℕ} (G : FiniteGraph n) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), k ≤ s.card ∧ Independent G s

def independenceNumberAtMost {n : ℕ} (G : FiniteGraph n) (k : ℕ) : Prop :=
  ∀ s : Finset (Fin n), Independent G s → s.card ≤ k

structure UnitDistanceConfiguration (n : ℕ) where
  points : Fin n → EuclideanSpace ℝ (Fin 2)
  graph : FiniteGraph n
  separated :
    ∀ ⦃i j : Fin n⦄, i ≠ j → 1 ≤ dist (points i) (points j)
  unit_edge :
    ∀ ⦃i j : Fin n⦄, i ≠ j →
      (graph.edge i j = true ↔ dist (points i) (points j) = 1)

def recordBounds : List ℚ :=
  [8 / 31, 5 / 16, 6 / 19, 9 / 35, 1 / 3, 1 / 4]

def emptyGraph : FiniteGraph 1 :=
  ⟨fun _ _ => false⟩

def completeGraphTwo : FiniteGraph 2 :=
  ⟨fun i j => decide (i ≠ j)⟩

theorem witness_pos :
    HasIndependentSetAtLeast emptyGraph 1 := by
  refine ⟨{0}, by simp, ?_⟩
  intro i j hi hj hne
  have hi' : i = (0 : Fin 1) := by
    simpa using hi
  have hj' : j = (0 : Fin 1) := by
    simpa using hj
  subst i
  subst j
  exact (hne rfl).elim

theorem witness_neg :
    ¬ HasIndependentSetAtLeast completeGraphTwo 2 := by
  intro h
  rcases h with ⟨s, hs, hInd⟩
  have hc : s.card ≤ 2 := by
    have h := Finset.card_le_card (Finset.subset_univ s)
    simpa using h
  have hs0 : (0 : Fin 2) ∈ s := by
    by_contra h0
    have hsub : s ⊆ ({1} : Finset (Fin 2)) := by
      intro x hx
      fin_cases x
      · exact False.elim (h0 hx)
      · simp
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega
  have hs1 : (1 : Fin 2) ∈ s := by
    by_contra h1
    have hsub : s ⊆ ({0} : Finset (Fin 2)) := by
      intro x hx
      fin_cases x
      · simp
      · exact False.elim (h1 hx)
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega
  have e := hInd hs0 hs1 (by decide)
  simpa [completeGraphTwo] using e

theorem problem_1066 :
    (∀ n : ℕ, ∀ C : UnitDistanceConfiguration n,
      HasIndependentSetAtLeast C.graph (8 * n / 31)) ∧
    (∀ ε : ℚ, 0 < ε →
      ∃ n : ℕ, ∃ C : UnitDistanceConfiguration n,
        n ≠ 0 ∧
        ∀ s : Finset (Fin n), Independent C.graph s →
          (s.card : ℚ) / n < 8 / 31 + ε) := by
  sorry

end