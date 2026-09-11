import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def Triple (m : ℕ) :=
  {s : Finset (Fin m) // s.card = 3}

def RamseyProperty (m n : ℕ) : Prop :=
  ∀ colouring : Triple m → Bool,
    ∃ S : Finset (Fin m),
      S.card = n ∧
        ∃ b : Bool,
          ∀ e : Triple m, e.1 ⊆ S → colouring e = b

noncomputable def R₃ (n : ℕ) : ℕ :=
  sInf {m : ℕ | RamseyProperty m n}

theorem witness_pos : RamseyProperty 3 1 := by
  intro colouring
  refine ⟨{0}, by simp, false, ?_⟩
  intro e h
  have hc : e.1.card ≤ ({0} : Finset (Fin 3)).card :=
    Finset.card_le_card h
  rw [e.2] at hc
  simp at hc

theorem witness_neg : ¬ RamseyProperty 2 3 := by
  intro h
  obtain ⟨S, hS, b, hb⟩ := h (fun _ => false)
  have hc : S.card ≤ (Finset.univ : Finset (Fin 2)).card :=
    Finset.card_le_card (Finset.subset_univ S)
  simp at hc
  omega

theorem erdos_problem_564 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ ((2 : ℝ) ^ (c * (n : ℝ))) ≤ (R₃ n : ℝ) := by
  sorry

end