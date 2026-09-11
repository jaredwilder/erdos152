import Mathlib


noncomputable section
open scoped BigOperators
/-- The `n`-th prime, with indexing beginning at `0`.  Thus this is `p_(n+1)`
    when the primes in the source are indexed beginning at `1`. -/
def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- The convergence assertion for the series in Erdos problem 15. -/
def primeSeriesConverges : Prop :=
  Summable (fun n : ℕ =>
    (-1 : ℝ) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) / (primeAt n : ℝ))

/-- A finite prefix of the same alternating-series expression, for use in
    concrete decidable witnesses. -/
def seriesPrefixSum (q : ℕ → ℕ) (N : ℕ) : ℚ :=
  Finset.sum (Finset.range N) (fun n =>
    (-1 : ℚ) ^ (n + 1) * ((n + 1 : ℕ) : ℚ) / (q n : ℚ))

/-- A decidable finite analogue of the series predicate. -/
def seriesPrefixIsZero (q : ℕ → ℕ) (N : ℕ) : Prop :=
  seriesPrefixSum q N = 0

theorem witness_pos :
    seriesPrefixIsZero (fun n : ℕ => if n = 0 then 1 else 2) 2 := by
  norm_num [seriesPrefixIsZero, seriesPrefixSum, Finset.sum_range_succ]

theorem witness_neg :
    ¬ seriesPrefixIsZero (fun _ : ℕ => 1) 1 := by
  norm_num [seriesPrefixIsZero, seriesPrefixSum, Finset.sum_range_succ]

/-- The open conjecture from Erdos problem 15.  The source's lower bound `1`
    is absorbed into the reindexing `n + 1`. -/
theorem erdos_problem_15 : primeSeriesConverges := by
  sorry

end