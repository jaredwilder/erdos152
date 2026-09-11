import Mathlib

open Set
open scoped BigOperators

noncomputable section

def problemNumber : ℕ := 1039

def polynomial (n : ℕ) (roots : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z - roots i)

def admissible (n : ℕ) (roots : Fin n → ℂ) : Prop :=
  ∀ i, ‖roots i‖ ≤ (1 : ℝ)

def sublevelSet (n : ℕ) (roots : Fin n → ℂ) : Set ℂ :=
  {z | ‖polynomial n roots z‖ < (1 : ℝ)}

def containsDisc (n : ℕ) (roots : Fin n → ℂ) (c : ℂ) (r : ℝ) : Prop :=
  Metric.ball c r ⊆ sublevelSet n roots

noncomputable def rho (n : ℕ) (roots : Fin n → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, containsDisc n roots c r}

def pommerenkeScale (n : ℕ) : ℝ :=
  1 / (2 * Real.exp 1 * (n : ℝ)^2)

def klrScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.sqrt (Real.log (n : ℝ)))

def powerMinusOne (n : ℕ) (z : ℂ) : ℂ :=
  z^n - 1

def powerMinusOneSublevel (n : ℕ) : Set ℂ :=
  {z | ‖powerMinusOne n z‖ < (1 : ℝ)}

noncomputable def powerMinusOneRho (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ c : ℂ, Metric.ball c r ⊆ powerMinusOneSublevel n}

def pommerenkeBound : Prop :=
  ∀ (n : ℕ) (roots : Fin n → ℂ),
    admissible n roots →
      pommerenkeScale n ≤ rho n roots

def klrBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (roots : Fin n → ℂ),
      2 ≤ n →
      admissible n roots →
        C * klrScale n ≤ rho n roots

def inverseLinearBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (roots : Fin n → ℂ),
      1 ≤ n →
      admissible n roots →
        C / (n : ℝ) ≤ rho n roots

def powerMinusOneUpperBound : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    powerMinusOneRho n ≤ (Real.pi / 2) / (n : ℝ)

theorem witness_pos :
    admissible 1 (fun _ : Fin 1 => (0 : ℂ)) := by
  intro i
  simp

theorem witness_neg :
    ¬ admissible 1 (fun _ : Fin 1 => (2 : ℂ)) := by
  intro h
  have hh := h ⟨0, by decide⟩
  norm_num [admissible] at hh

theorem erdos_1039 :
    inverseLinearBound := by
  sorry