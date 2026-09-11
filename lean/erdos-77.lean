import Mathlib

noncomputable section

-- Numeric literals occurring in the source entry: 77, 100, 1000, 88, 4, 2, 1,
-- 128, 3.7992, 23, 24, 93, 3, 1029, 627, 5, 6.
def sourceNumerals : List ℚ :=
  [77, 100, 1000, 88, 4, 2, 1, 128, 3.7992, 23, 24, 93, 3, 1029, 627, 5, 6]

def Coloring (n : ℕ) := Fin n → Fin n → Bool

def IsTwoColoring {n : ℕ} (c : Coloring n) : Prop :=
  ∀ i j : Fin n, c i j = c j i

def HasMonochromaticClique (c : Coloring n) (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin n,
    Function.Injective f ∧
      ∃ b : Bool, ∀ i j : Fin k, i ≠ j → c (f i) (f j) = b

def RamseyProperty (n k : ℕ) : Prop :=
  ∀ c : Coloring n, IsTwoColoring c → HasMonochromaticClique c k

theorem witness_pos : RamseyProperty 1 1 := by
  intro c _
  refine ⟨(fun _ : Fin 1 => (0 : Fin 1)), ?_, ?_⟩
  · intro i j _
    exact Subsingleton.elim _ _
  · refine ⟨c 0 0, ?_⟩
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim

theorem witness_neg : ¬ RamseyProperty 1 2 := by
  intro h
  have H := h (fun _ _ => false) (by
    intro i j
    rfl)
  rcases H with ⟨f, hf, b, hb⟩
  have e : (0 : Fin 2) = 1 := by
    apply hf
    exact Subsingleton.elim _ _
  have hne : (0 : Fin 2) ≠ 1 := by
    omega
  exact hne e

noncomputable def ramseyNumber (k : ℕ) : ℕ := by
  classical
  exact
    if h : ∃ n : ℕ, RamseyProperty n k then
      Nat.find h
    else
      0

def ramseySequence (k : ℕ) : ℝ :=
  Real.rpow (ramseyNumber k : ℝ) (1 / (k : ℝ))

def ramseyLimitExists : Prop :=
  ∃ L : ℝ, Filter.Tendsto ramseySequence Filter.atTop (nhds L)

theorem ramsey_limit_exists : ramseyLimitExists := by
  sorry