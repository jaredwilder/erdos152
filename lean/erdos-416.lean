import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem 416.

The solvability predicate is represented by a finite search.  The factorial
cutoff is a concrete decidable encoding of the inverse-totient question.
-/

-- The numerical labels and constants occurring in the source include:
-- 416, 74, 79, 80, 98, 29, 35, 2, 1, 88, 36, 04, 821, 2025, 2026, 0, 3.

def totientSolvable (n : ℕ) : Prop :=
  ∃ m ∈ Finset.Icc 0 (Nat.factorial (n + 1)),
    Nat.totient m = n

instance (n : ℕ) : Decidable (totientSolvable n) := by
  unfold totientSolvable
  infer_instance

def V (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter totientSolvable).card

def RatioLimitQuestion : Prop :=
  Filter.Tendsto
    (fun x : ℕ => (V (2 * x) : ℝ) / (V x : ℝ))
    Filter.atTop
    (nhds (2 : ℝ))

def AsymptoticFormulaQuestion : Prop :=
  ∃ f : ℕ → ℝ,
    Filter.Tendsto
      (fun x : ℕ => (V x : ℝ) / f x)
      Filter.atTop
      (nhds (1 : ℝ))

theorem witness_pos : totientSolvable 1 := by
  decide

theorem witness_neg : ¬ totientSolvable 3 := by
  decide

theorem main_conjecture : RatioLimitQuestion := by
  sorry

end
