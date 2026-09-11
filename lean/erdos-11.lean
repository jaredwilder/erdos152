import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  The source asks whether every sufficiently large odd natural number is the
  sum of a squarefree natural number and a power of 2.

  Numerical data appearing in the source resolution includes:
  #11, 77, 80, 96, 28, 85, 90, 92, 97, 10^7, 24, 2^50,
  1.12×10^15, 1, 2, 4, 9, 10, 16, 19, 98, 2026, 8, 30, and 0.
-/

/-- A positive natural number is squarefree when no square of an integer
    between 2 and the number divides it. -/
def SquarefreeNat (n : ℕ) : Prop :=
  0 < n ∧ ∀ d ∈ Finset.Icc 2 n, ¬(d * d ∣ n)

/-- A natural number is a power of 2, with an explicit bound sufficient for
    checking whether it can occur in a representation of `n`. -/
def IsPowerOfTwoUpTo (m n : ℕ) : Prop :=
  ∃ k ∈ Finset.range (n + 1), 2 ^ k = m

/-- `n` has the required representation, with all witnesses bounded by `n`. -/
def Represents (n : ℕ) : Prop :=
  ∃ a ∈ Finset.range (n + 1),
    SquarefreeNat a ∧
      ∃ m ∈ Finset.range (n + 1), IsPowerOfTwoUpTo m n ∧ a + m = n

theorem witness_pos : Represents 3 := by
  refine ⟨1, by norm_num, ?_, 2, by norm_num, ?_, by norm_num⟩
  · refine ⟨by norm_num, ?_⟩
    intro d hd
    simp only [Finset.mem_Icc] at hd
    omega
  · exact ⟨1, by norm_num, by norm_num⟩

theorem witness_neg : ¬ Represents 1 := by
  intro h
  rcases h with ⟨a, ha, hsq, m, hm, hp, hsum⟩
  have ha_pos : 0 < a := hsq.1
  rcases hp with ⟨k, hk, hpow⟩
  have hm_pos : 0 < m := by
    rw [← hpow]
    positivity
  omega

/-- Erdős problem 11: every sufficiently large odd natural number has the
    required representation. -/
theorem erdos_problem_11 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → Represents n := by
  sorry

end