import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- A finite, decidable shadow of the hypotheses on an increasing sequence of
positive integers. -/
def FiniteHypotheses (s : List ℕ) : Prop :=
  s.Pairwise (· < ·) ∧ ∀ x ∈ s, 0 < x

theorem witness_pos : FiniteHypotheses [1, 2] := by
  norm_num [FiniteHypotheses, List.pairwise_cons]

theorem witness_neg : ¬ FiniteHypotheses [1, 1] := by
  norm_num [FiniteHypotheses, List.pairwise_cons]

/-- Erdős problem 260, with the sequence indexed from `0`; thus `n + 1`
corresponds to the original positive index `n`. -/
def Erdos260Statement : Prop :=
  ∀ (a : ℕ → ℕ),
    (∀ n, 0 < a n) →
    StrictMono a →
    Filter.Tendsto
      (fun n : ℕ => (a n : ℝ) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop →
    Irrational (∑' n : ℕ, (a n : ℝ) / (2 : ℝ) ^ (a n))

theorem erdos_260 : Erdos260Statement := by
  sorry

end