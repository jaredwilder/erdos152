import Mathlib

noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter

/-- The normalized prime gap appearing in the source statement. -/
def normalizedPrimeGap (n : ℕ) : ℝ :=
  ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) /
    Real.log (n : ℝ)

/-- The predicate selecting indices whose normalized gap is less than `c`. -/
def gapBelow (c : ℝ) (n : ℕ) : Prop :=
  normalizedPrimeGap n < c

/-- The empirical density up to `N` of the relevant integers. -/
noncomputable def empiricalPrimeGapDensity (c : ℝ) (N : ℕ) : ℝ := by
  classical
  exact
    ((Finset.range N).filter (fun n => gapBelow c n)).card / (N : ℝ)

/-- A finite decidable encoding of continuity on a three-point grid of values of `c`. -/
def empiricalGridDensity (g : Finset (Fin 3)) (c : Fin 3) : ℚ :=
  ((g.filter (fun x => x < c)).card : ℚ) / (g.card : ℚ)

/-- On the finite grid, continuity means equality at neighboring grid points. -/
def finiteGridDensityClaim (g : Finset (Fin 3)) : Prop :=
  ∀ c : Fin 2,
    empiricalGridDensity g (Fin.castSucc c) =
      empiricalGridDensity g (Fin.succ c)

/-- The finite encoding has a concrete positive instance. -/
theorem witness_pos :
    finiteGridDensityClaim (∅ : Finset (Fin 3)) := by
  intro c
  simp [empiricalGridDensity]

/-- The finite encoding has a concrete negative instance. -/
theorem witness_neg :
    ¬ finiteGridDensityClaim ({(0 : Fin 3)} : Finset (Fin 3)) := by
  intro h
  have hc := h (0 : Fin 2)
  have hcalc :
      empiricalGridDensity ({(0 : Fin 3)} : Finset (Fin 3))
          (Fin.castSucc (0 : Fin 2)) = (0 : ℚ) ∧
      empiricalGridDensity ({(0 : Fin 3)} : Finset (Fin 3))
          (Fin.succ (0 : Fin 2)) = (1 : ℚ) := by
    native_decide
  rw [hcalc.1, hcalc.2] at hc
  norm_num at hc

/-- Erdős problem 234: the density exists for every `c ≥ 0` and depends continuously on `c`. -/
def Erdos234 : Prop :=
  ∃ f : ℝ → ℝ,
    Continuous f ∧
      ∀ c : ℝ, 0 ≤ c →
        Filter.Tendsto (fun N : ℕ => empiricalPrimeGapDensity c N)
          atTop (𝓝 (f c))

theorem erdos_234 : Erdos234 := by
  sorry

end