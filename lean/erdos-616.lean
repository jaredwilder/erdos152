import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def IsCover {n : ℕ} (H : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ e ∈ H, (e ∩ S).Nonempty

def CoverAtMost {n : ℕ} (H : Finset (Finset (Fin n))) (t : ℚ) : Prop :=
  ∃ S : Finset (Fin n), (S.card : ℚ) ≤ t ∧ IsCover H S

def Uniform {r n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = r

def LocalOne {r n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ U : Finset (Fin n), U.card ≤ 3 * r - 3 →
    ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ e ∈ H, e ⊆ U → (e ∩ S).Nonempty

def Claim (r n : ℕ) (H : Finset (Finset (Fin n))) (t : ℚ) : Prop :=
  Uniform (r := r) H → LocalOne (r := r) H → CoverAtMost H t

def Good (r : ℕ) (t : ℚ) : Prop :=
  ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)), Claim r n H t

def Optimal (r : ℕ) (t : ℚ) : Prop :=
  Good r t ∧ ∀ u : ℚ, Good r u → t ≤ u

theorem witness_pos :
    Claim 3 1 (∅ : Finset (Finset (Fin 1))) 0 := by
  unfold Claim
  intro _ _
  refine ⟨∅, by simp, ?_⟩
  intro e he
  simp at he

theorem witness_neg :
    ¬ Claim 3 3 ({(Finset.univ : Finset (Fin 3))} : Finset (Finset (Fin 3))) 0 := by
  intro h
  have hu : Uniform (r := 3)
      ({(Finset.univ : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
    intro e he
    have he' : e = (Finset.univ : Finset (Fin 3)) := by
      simpa using he
    subst e
    simp
  have hl : LocalOne (r := 3)
      ({(Finset.univ : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
    intro U hU
    refine ⟨{0}, by simp, ?_⟩
    intro e he hsub
    have he' : e = (Finset.univ : Finset (Fin 3)) := by
      simpa using he
    subst e
    simp
  obtain ⟨S, hcard, hcover⟩ := h hu hl
  have hcard' : (S.card : ℚ) = 0 := by
    apply le_antisymm hcard
    positivity
  have hs : S.card = 0 := by
    exact_mod_cast hcard'
  have hS : S = ∅ := Finset.card_eq_zero.mp hs
  have hne : ((Finset.univ : Finset (Fin 3)) ∩ S).Nonempty :=
    hcover _ (by simp)
  simpa [hS] using hne

theorem erdos_616 :
    ∀ r : ℕ, 3 ≤ r →
      ∃ t : ℚ, Optimal r t ∧
        ((3 : ℚ) / 16) * r + 7 / 8 ≤ t ∧
        t ≤ ((1 : ℚ) / 5) * r := by
  sorry

end