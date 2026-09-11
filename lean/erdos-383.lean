import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Source numerals retained here include 0, 1, 2, 383, 382, 80, 2026, 8, and 30.
The finite bound in the definition below makes the predicate decidable: every
prime divisor of a positive natural number is at most that number.
-/

def erdosProduct (k p : ℕ) : ℕ :=
  Finset.prod (Finset.range (k + 1)) (fun i => p ^ 2 + i)

def largestPrimeDivisorIs (k p : ℕ) : Prop :=
  Nat.Prime p ∧
    p ∣ erdosProduct k p ∧
      ∀ q ∈ Finset.range (erdosProduct k p + 1),
        Nat.Prime q → q ∣ erdosProduct k p → q ≤ p

/-- The Erdős problem #383: for every k, infinitely many such primes p exist. -/
theorem erdos_383 :
    ∀ k : ℕ, ∀ N : ℕ, ∃ p : ℕ, N < p ∧ largestPrimeDivisorIs k p := by
  sorry

theorem witness_pos : largestPrimeDivisorIs 0 2 := by
  unfold largestPrimeDivisorIs erdosProduct
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro q hq hp hd
  have hq5 : q < 5 := by
    simpa [Finset.mem_range, Finset.prod_range_succ] using hq
  interval_cases q <;> norm_num at *

theorem witness_neg : ¬ largestPrimeDivisorIs 1 2 := by
  intro h
  rcases h with ⟨hp, hd, hmax⟩
  have h5 : 5 ∈ Finset.range (erdosProduct 1 2 + 1) := by
    norm_num [erdosProduct, Finset.prod_range_succ]
  have h := hmax 5 h5 (by norm_num) (by norm_num [erdosProduct, Finset.prod_range_succ])
  norm_num at h

end