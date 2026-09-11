import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def NonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ s ∈ (A.erase a).powerset,
    s.Nonempty → ¬ a ∣ s.sum id

def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ NonDividing A

def F (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter NonDividing).sup Finset.card

def explicitUpperBound : Prop :=
  ∀ N : ℕ, F N < 3 * Nat.sqrt N + 1

def CsabaExponent : ℝ :=
  (1 : ℝ) / 5

def PhamZakharovExponent : ℝ :=
  (1 : ℝ) / 4

def StrausConstant : ℝ :=
  Real.sqrt (2 / Real.log 2)

def HalfPowerQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (F N : ℝ) > (N : ℝ) ^ (1 / 2 - ε)

def problemNumber : ℕ := 131

theorem witness_pos : Admissible 1 ({1} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp at ha
    subst a
    simp
  · intro a ha s hs hne
    simp at ha
    subst a
    have hs' : s ⊆ ({1} : Finset ℕ).erase 1 :=
      Finset.mem_powerset.mp hs
    have : s = ∅ := by
      simpa using hs'
    subst s
    simp at hne

theorem witness_neg : ¬ Admissible 2 ({1, 2} : Finset ℕ) := by
  intro h
  have hbad := h.2 1 (by simp) {2} (by simp) (by simp)
  norm_num at hbad

theorem erdos_131_resolution : ¬ HalfPowerQuestion := by
  sorry

end