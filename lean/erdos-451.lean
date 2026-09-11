import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-
  The product over `1 ≤ i ≤ k` is represented by `i ∈ Finset.range k`
  and the factor `n - (i + 1)`.
-/
def intervalProduct (k n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n - (i + 1))

def PrimeFactorFree (k n : ℕ) : Prop :=
  ∀ p ∈ Finset.Icc (k + 1) (2 * k - 1),
    Nat.Prime p → ¬ p ∣ intervalProduct k n

def Good (k n : ℕ) : Prop :=
  2 * k < n ∧ PrimeFactorFree k n

def IsNk (k n : ℕ) : Prop :=
  Good k n ∧ ∀ m : ℕ, Good k m → n ≤ m

theorem witness_pos : Good 1 3 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hprime hdiv
  have hb := Finset.mem_Icc.mp hp
  omega

theorem witness_neg : ¬ Good 1 2 := by
  intro h
  have hlt : 2 * 1 < 2 := h.1
  norm_num at hlt

theorem open_estimate :
    ∀ d : ℕ, 0 < d →
      ∀ᶠ k : ℕ in Filter.atTop,
        ∃ n : ℕ, IsNk k n ∧ (k : ℝ) ^ d < (n : ℝ) := by
  sorry

end