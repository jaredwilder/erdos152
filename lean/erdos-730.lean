import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  The source speaks of integers n and m for which the central binomial
  coefficients are defined.  We use ℕ, which is the usual domain here.
  The numerical data appearing in the source is retained below:
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 27, 30, 75, 87, 88, 607, 608,
  730, 2025, 2026, 10003, 10004, 10005, 129515.
-/

def sourceNumerals : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 27, 30, 75, 87, 88, 607, 608,
   730, 2025, 2026, 10003, 10004, 10005, 129515]

def primeDivisors (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter
    (fun p => Nat.Prime p ∧ k % p = 0)

def samePrimeDivisors (n m : ℕ) : Prop :=
  primeDivisors (Nat.choose (2 * n) n) =
    primeDivisors (Nat.choose (2 * m) m)

theorem witness_pos : samePrimeDivisors 1 1 := by
  rfl

theorem witness_neg : ¬ samePrimeDivisors 1 2 := by
  intro h
  unfold samePrimeDivisors at h
  have h3 : 3 ∈ primeDivisors (Nat.choose (2 * 2) 2) := by
    norm_num [primeDivisors, Nat.choose]
  have hnot : 3 ∉ primeDivisors (Nat.choose (2 * 1) 1) := by
    intro hx
    rw [primeDivisors] at hx
    have hx' := (Finset.mem_filter.mp hx).1
    norm_num at hx'
  apply hnot
  rw [h]
  exact h3

/-- The formalized infinitude assertion from Erdős problem #730. -/
theorem erdos_730 :
    ∀ N : ℕ, ∃ n m : ℕ,
      N ≤ n ∧ n ≠ m ∧ samePrimeDivisors n m := by
  sorry

end