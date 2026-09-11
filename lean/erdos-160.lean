import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- A positive step together with four equally spaced points in `Fin N`. -/
def IsFourAP {N : ℕ} (a b c d : Fin N) : Prop :=
  ∃ r : Fin N,
    0 < r.val ∧
      b.val = a.val + r.val ∧
      c.val = a.val + 2 * r.val ∧
      d.val = a.val + 3 * r.val

/-- The four colours contain at least three distinct colours. -/
def HasThreeColors {N k : ℕ} (f : Fin N → Fin k)
    (a b c d : Fin N) : Prop :=
  3 ≤ ({f a, f b, f c, f d} : Finset (Fin k)).card

/-- `N` admits a colouring with `k` colours satisfying the required condition. -/
def Admissible (N k : ℕ) : Prop :=
  ∃ f : Fin N → Fin k,
    ∀ a b c d : Fin N, IsFourAP a b c d → HasThreeColors f a b c d

instance (N k : ℕ) : Decidable (Admissible N k) := by
  unfold Admissible HasThreeColors IsFourAP
  infer_instance

theorem admissible_self (N : ℕ) : Admissible N N := by
  refine ⟨id, ?_⟩
  intro a b c d hAP
  obtain ⟨r, hr, hba, hca, hda⟩ := hAP
  have habv : a.val < b.val := by omega
  have hbcv : b.val < c.val := by omega
  have hcdv : c.val < d.val := by omega
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hac : a ≠ c := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have had : a ≠ d := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hbc : b ≠ c := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hbd : b ≠ d := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hcd : c ≠ d := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hsub :
      ({a, b, c} : Finset (Fin N)) ⊆ ({a, b, c, d} : Finset (Fin N)) := by
    simp
  have hcard : ({a, b, c} : Finset (Fin N)).card = 3 := by
    simp [hab, hac, hbc]
  have hcard' :
      3 ≤ ({a, b, c, d} : Finset (Fin N)).card := by
    calc
      3 = ({a, b, c} : Finset (Fin N)).card := hcard.symm
      _ ≤ ({a, b, c, d} : Finset (Fin N)).card := Finset.card_le_card hsub
  simpa [HasThreeColors] using hcard'

/-- The least number of colours required by the problem. -/
def h (N : ℕ) : ℕ :=
  Nat.find ⟨N, admissible_self N⟩

theorem h_spec (N : ℕ) : Admissible N (h N) :=
  Nat.find_spec ⟨N, admissible_self N⟩

theorem witness_pos : Admissible 4 3 := by
  decide

theorem witness_neg : ¬ Admissible 4 2 := by
  decide

def hunterExponent : ℝ :=
  Real.log 3 / Real.log 22

def OldUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      (h N : ℝ) ≤ C * (N : ℝ) ^ (2 / 3 : ℝ)

def HunterUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in Filter.atTop,
        (h N : ℝ) ≤ C * (N : ℝ) ^ (hunterExponent + ε)

def ExponentialLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (c * (Real.log (N : ℝ)) ^ (1 / 9 : ℝ)) ≤ (h N : ℝ)

/-
  Erdos problem #160.  The numerical value of log 3 / log 22 is approximately
  0.355, and the displayed bounds encode the estimates in the source.
-/
theorem erdos_problem_160 :
    OldUpperBound ∧ HunterUpperBound ∧ ExponentialLowerBound := by
  sorry

end