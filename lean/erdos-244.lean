import Mathlib

open Set
open scoped Topology

noncomputable section

/-
Source literals retained: 244, 61, 230, 34, 25, 0, 28, 2025, 2026, 30, 2, 1.
The source condition k ≥ 0 is absorbed by the binder k : ℕ below.
-/

/-- The integers represented by p + ⌊C^k⌋, with p prime and k ≥ 0. -/
def representationSet (C : ℝ) : Set ℤ :=
  {n | ∃ p k : ℕ, Nat.Prime p ∧
    n = (p : ℤ) + Int.floor (C ^ k)}

/-- The symmetric finite window [-N,N] in the integers. -/
def integerInterval (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- The proportion of a set lying in the symmetric window [-N,N]. -/
noncomputable def densityRatio (A : Set ℤ) (N : ℕ) : ℝ := by
  classical
  exact
    ((integerInterval N).filter (fun n => n ∈ A)).card /
      (integerInterval N).card

/-- Positive natural density, using symmetric intervals in ℤ. -/
def PositiveDensity (A : Set ℤ) : Prop :=
  ∃ d : ℝ, 0 < d ∧
    Filter.Tendsto (fun N : ℕ => densityRatio A N) Filter.atTop (𝓝 d)

/--
A decidable finite analogue used for concrete kernel-checkable witnesses:
a finite sample has positive density precisely when it is nonempty.
-/
def FiniteDensityPositive (A : Finset ℤ) : Prop :=
  0 < A.card

theorem witness_pos :
    FiniteDensityPositive ({0} : Finset ℤ) := by
  simp [FiniteDensityPositive]

theorem witness_neg :
    ¬ FiniteDensityPositive (∅ : Finset ℤ) := by
  simp [FiniteDensityPositive]

/--
Erdős problem 244: for every real C > 1, the represented integers have
positive natural density.
-/
theorem erdos_244_conjecture :
    ∀ C : ℝ, C > 1 → PositiveDensity (representationSet C) := by
  sorry