import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology

def Sequence := ℕ → ℕ

def StrictlyIncreasing (a : Sequence) : Prop :=
  ∀ n : ℕ, a n < a (n + 1)

def HasRequiredLimit (a : Sequence) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
    Filter.atTop (𝓝 (1 : ℝ))

def HasRationalReciprocalSum (a : Sequence) : Prop :=
  ∃ q : ℚ,
    HasSum (fun n : ℕ => (1 : ℝ) / (a n : ℝ)) (q : ℝ)

def recurrencePredicate (a : Sequence) (n : ℕ) : Prop :=
  a (n + 1) = a n ^ 2 - a n + 1

def EventuallyRecurrence (a : Sequence) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → recurrencePredicate a n

def ProblemHypotheses (a : Sequence) : Prop :=
  1 ≤ a 0 ∧ StrictlyIncreasing a ∧
    HasRequiredLimit a ∧ HasRationalReciprocalSum a

theorem erdos_243 :
    ∀ a : Sequence,
      ProblemHypotheses a → EventuallyRecurrence a := by
  sorry

theorem witness_pos :
    recurrencePredicate (fun _ : ℕ => 1) 0 := by
  norm_num [recurrencePredicate]

theorem witness_neg :
    ¬ recurrencePredicate (fun n : ℕ => n + 1) 0 := by
  norm_num [recurrencePredicate]

end