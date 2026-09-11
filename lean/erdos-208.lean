import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- A decidable version of the assertion that a positive natural number is squarefree. -/
def squarefreeNat (n : ℕ) : Prop :=
  0 < n ∧ ∀ p ∈ Finset.Icc 2 n, ¬(p ^ 2 ∣ n)

/-- There is a squarefree number strictly after `n` and no farther than `r` away. -/
def hasSquarefreeWithin (n : ℕ) (r : ℝ) : Prop :=
  ∃ m : ℕ, n < m ∧ (m : ℝ) ≤ (n : ℝ) + r ∧ squarefreeNat m

/-- The eventual upper-bound formulation of a gap estimate. -/
def eventuallySquarefreeWithin (f : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → hasSquarefreeWithin n (f n)

/--
The two questions in Erdős problem 208, with `o(1)` expressed in the
usual epsilon formulation.
-/
def Erdos208 : Prop :=
  (∀ ε : ℝ, 0 < ε →
    eventuallySquarefreeWithin (fun n : ℕ => (n : ℝ) ^ ε)) ∧
  (∀ ε : ℝ, 0 < ε →
    eventuallySquarefreeWithin
      (fun n : ℕ =>
        (1 + ε) * (Real.pi ^ 2 / 6) *
          (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))))

theorem witness_pos : squarefreeNat 6 := by
  unfold squarefreeNat
  constructor
  · norm_num
  · intro p hp
    rcases (Finset.mem_Icc.mp hp) with ⟨hlo, hhi⟩
    interval_cases p <;> norm_num

theorem witness_neg : ¬ squarefreeNat 4 := by
  unfold squarefreeNat
  intro h
  have hnot : ¬ ((2 : ℕ) ^ 2 ∣ 4) :=
    h.2 2 (by norm_num)
  norm_num at hnot

theorem erdos_208 : Erdos208 := by
  sorry

end