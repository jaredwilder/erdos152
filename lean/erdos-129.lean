import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def IsEdgeColoring {N r : ℕ} (c : Fin N → Fin N → Fin r) : Prop :=
  ∀ i j, i ≠ j → c i j = c j i

def IsMonochromaticClique {N k r : ℕ}
    (c : Fin N → Fin N → Fin r) (T : Finset (Fin N)) (col : Fin r) : Prop :=
  T.card = k ∧
    ∀ a ∈ T, ∀ b ∈ T, a ≠ b → c a b = col

def AvoidsMonochromaticClique {N k r : ℕ}
    (c : Fin N → Fin N → Fin r) (S : Finset (Fin N)) (col : Fin r) : Prop :=
  ¬ ∃ T : Finset (Fin N), T ⊆ S ∧ IsMonochromaticClique (k := k) c T col

def RamseyGood (n k r N : ℕ) : Prop :=
  ∀ c : Fin N → Fin N → Fin r,
    IsEdgeColoring c →
      ∃ S : Finset (Fin N), S.card = n ∧
        ∃ col : Fin r, AvoidsMonochromaticClique (k := k) c S col

noncomputable def ramseyNumber (n k r : ℕ) : ℕ :=
  by
    classical
    by_cases h : ∃ N : ℕ, RamseyGood n k r N
    · exact Nat.find h
    · exact 0

theorem witness_pos : RamseyGood 1 3 1 1 := by
  intro c hc
  refine ⟨{0}, by simp, 0, ?_⟩
  intro h
  obtain ⟨T, hTS, hmono⟩ := h
  have hle : T.card ≤ 1 := by
    simpa using Finset.card_le_card hTS
  have hcard : T.card = 3 := hmono.1
  omega

theorem witness_neg : ¬ RamseyGood 3 3 1 3 := by
  intro h
  let c : Fin 3 → Fin 3 → Fin 1 := fun _ _ => 0
  have hc : IsEdgeColoring c := by
    intro i j hij
    rfl
  obtain ⟨S, hScard, col, havoid⟩ := h c hc
  have hcol : col = 0 := Fin.eq_zero col
  apply havoid
  refine ⟨S, subset_rfl, hScard, ?_⟩
  intro a ha b hb hab
  simp [c, hcol]

theorem erdos_problem_129 :
    ∀ r : ℕ, 1 < r →
      ∃ C : ℝ, 1 < C ∧
        ∀ n : ℕ,
          (ramseyNumber n 3 r : ℝ) < C ^ Real.sqrt (n : ℝ) := by
  sorry

end