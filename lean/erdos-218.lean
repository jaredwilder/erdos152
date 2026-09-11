import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter
/- Source numeric literals: 218, 55, 57, 61, 65, 85, 23, 141, 0, 1, 3/2. -/

def primeNumber (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

def primeGap (n : ℕ) : ℕ :=
  primeNumber (n + 1) - primeNumber n

def gapGe (d : ℕ → ℕ) (n : ℕ) : Prop :=
  d (n + 1) ≥ d n

def gapLe (d : ℕ → ℕ) (n : ℕ) : Prop :=
  d (n + 1) ≤ d n

def gapEq (d : ℕ → ℕ) (n : ℕ) : Prop :=
  d (n + 1) = d n

def hasDensity (P : ℕ → Prop) [DecidablePred P] (r : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ =>
      ((Finset.filter P (Finset.range N)).card : ℝ) / (N : ℝ))
    atTop (𝓝 r)

def infinitelyOften (P : ℕ → Prop) : Prop :=
  ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ P n

theorem witness_pos :
    gapGe (fun n : ℕ => n) 0 := by
  norm_num [gapGe]

theorem witness_neg :
    ¬ gapGe (fun n : ℕ => if n = 0 then 1 else 0) 0 := by
  norm_num [gapGe]

theorem erdosProblem218 :
    hasDensity (gapGe primeGap) (1 / 2 : ℝ) ∧
      hasDensity (gapLe primeGap) (1 / 2 : ℝ) ∧
      infinitelyOften (gapEq primeGap) := by
  sorry

end