import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- The function appearing in Erdos problem 411. -/
def g (n : ℕ) : ℕ :=
  n + Nat.totient n

/-- Iteration of `g`, with the zeroth iterate equal to the starting value. -/
def gIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => g (gIter k n)

/-- The eventual doubling property from the problem. -/
def EventuallyDoubles (n r : ℕ) : Prop :=
  ∃ K : ℕ, ∀ k : ℕ, K ≤ k → gIter (k + r) n = 2 * gIter k n

/-
Source numerical data from Erdos problem 411:
1, 2, 10, 94, 9, 25, 3114, 6, 729, 8, 7, 10^10, 35, 47,
4, 3, 738, 148646, 4325798, 411, 80, 81, 2025, 28, 2026, 30.
-/
def sourceNumerals : List ℕ :=
  [1, 2, 10, 94, 9, 25, 3114, 6, 729, 8, 7, 10000000000,
   35, 47, 4, 3, 738, 148646, 4325798, 411, 80, 81, 2025, 28, 2026, 30]

theorem iter_zero_zero (k : ℕ) : gIter k 0 = 0 := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      simp [gIter, g, ih]

theorem witness_pos : EventuallyDoubles 0 1 := by
  refine ⟨0, ?_⟩
  intro k hk
  simp [iter_zero_zero]

theorem iter_pos_one (k : ℕ) : 0 < gIter k 1 := by
  induction k with
  | zero =>
      simp [gIter]
  | succ k ih =>
      simp [gIter, g]
      omega

theorem witness_neg : ¬ EventuallyDoubles 1 0 := by
  intro h
  rcases h with ⟨K, hK⟩
  have e := hK K (le_refl K)
  simp at e
  have hp := iter_pos_one K
  omega

/--
Cambie's conjectural description of the positive solutions to the
doubling problem: only the shift `r = 2` occurs, and the starting
value is `2^l p` with `l ≥ 1` and
`p ∈ {2, 3, 5, 7, 35, 47}`.
-/
theorem open_conjecture :
    ∀ n r : ℕ,
      1 ≤ n →
      1 ≤ r →
      EventuallyDoubles n r →
        r = 2 ∧
          ∃ l p : ℕ,
            1 ≤ l ∧
            p ∈ ({2, 3, 5, 7, 35, 47} : Finset ℕ) ∧
            n = 2 ^ l * p := by
  sorry

end
