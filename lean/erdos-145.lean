import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter
/-
Erdős Problem 145.

The source asks about the sequence s₁ < s₂ < ⋯ of squarefree numbers and the
limit for every α ≥ 0.  The known unconditional ranges include 0 ≤ α ≤ 2,
α ≤ 3, α ≤ 11/3, and α ≤ 3.75; the all-α assertion follows from ABC.
We index the sequence from 0 in Lean, so its first term is s 0.
-/

def squarefree (n : ℕ) : Prop :=
  n ≠ 0 ∧
    ∀ p ∈ Finset.range (n + 1), Nat.Prime p → ¬ p ^ 2 ∣ n

theorem witness_pos : squarefree 1 := by
  unfold squarefree
  constructor
  · norm_num
  · intro p hp hprime
    have hp_lt : p < 2 := by
      simpa using (Finset.mem_range.mp hp)
    have hp_two : 2 ≤ p := hprime.two_le
    intro _
    omega

theorem witness_neg : ¬ squarefree 4 := by
  intro h
  have hbad := h.2 2 (by norm_num) (by norm_num)
  exact hbad (by norm_num)

def IsSquarefreeSequence (s : ℕ → ℕ) : Prop :=
  0 < s 0 ∧ StrictMono s ∧ ∀ m : ℕ, squarefree m ↔ ∃ n : ℕ, s n = m

def gapMomentAverage (s : ℕ → ℕ) (α : ℝ) (x : ℕ) : ℝ :=
  (1 / (x : ℝ)) *
    Finset.sum (Finset.range (x + 1)) (fun n =>
      if s n ≤ x then
        ((s (n + 1) - s n : ℕ) : ℝ) ^ α
      else
        0)

def HasGapMomentLimit (s : ℕ → ℕ) (α : ℝ) : Prop :=
  ∃ L : ℝ,
    Filter.Tendsto (fun x : ℕ => gapMomentAverage s α x) atTop (𝓝 L)

def ErdosProblem145 : Prop :=
  ∀ α : ℝ, 0 ≤ α →
    ∃ s : ℕ → ℕ, IsSquarefreeSequence s ∧ HasGapMomentLimit s α

theorem erdos_problem_145 : ErdosProblem145 := by
  sorry

end