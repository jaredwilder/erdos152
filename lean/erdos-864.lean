import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def representations (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n)

def containedInInterval (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

def exceptionalCount (N : ℕ) (A : Finset ℕ) : ℕ :=
  ((Finset.range (2 * N + 1)).filter
    (fun n => 1 < (representations A n).card)).card

def hasAtMostOneException (N : ℕ) (A : Finset ℕ) : Prop :=
  containedInInterval N A ∧ exceptionalCount N A ≤ 1

theorem witness_pos :
    hasAtMostOneException 3 ({1, 2} : Finset ℕ) := by
  norm_num [hasAtMostOneException, containedInInterval, exceptionalCount,
    representations, Finset.filter, Finset.product, Finset.range] <;> decide

theorem witness_neg :
    ¬ hasAtMostOneException 4 ({1, 2, 3, 4} : Finset ℕ) := by
  norm_num [hasAtMostOneException, containedInInterval, exceptionalCount,
    representations, Finset.filter, Finset.product, Finset.range] <;> decide

theorem conjectured_asymptotic_upper_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ, hasAtMostOneException N A →
          (A.card : ℝ) ≤
            (1 + ε) * (2 / Real.sqrt 3) * Real.sqrt (N : ℝ) := by
  sorry

end