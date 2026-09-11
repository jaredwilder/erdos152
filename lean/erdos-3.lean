import Mathlib


noncomputable section
open scoped BigOperators
/-
Erdős problem 3: If A ⊆ ℕ has divergent harmonic sum, must A contain
arbitrarily long arithmetic progressions?
-/

def IsArithmeticProgression (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin k, a + i.val * d ∈ A

def HasArbitrarilyLongProgressions (A : Set ℕ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → IsArithmeticProgression A k

noncomputable def HarmonicDiverges (A : Set ℕ) : Prop :=
  by
    classical
    exact
      Filter.Tendsto
        (fun N : ℕ =>
          Finset.sum (Finset.range N) (fun n =>
            if n ∈ A then (1 : ℝ) / (n : ℝ) else 0))
        Filter.atTop Filter.atTop

/-- A decidable finite analogue: all progression parameters are bounded
by the largest element of the finite set. -/
def FinsetHasArithmeticProgression (s : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : Fin (s.sup (fun n : ℕ => n) + 1),
    0 < d.val ∧ ∀ i : Fin k, a.val + i.val * d.val ∈ s

theorem witness_pos :
    FinsetHasArithmeticProgression ({1, 2, 3} : Finset ℕ) 3 := by
  unfold FinsetHasArithmeticProgression
  decide

theorem witness_neg :
    ¬ FinsetHasArithmeticProgression ({1, 2, 4} : Finset ℕ) 3 := by
  unfold FinsetHasArithmeticProgression
  decide

theorem erdos_problem_3 :
    ∀ A : Set ℕ,
      HarmonicDiverges A → HasArbitrarilyLongProgressions A := by
  sorry

end