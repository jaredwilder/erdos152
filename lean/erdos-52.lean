import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def sumset (A : Finset ℤ) : Finset ℤ :=
  (A.product A).image (fun p : ℤ × ℤ => p.1 + p.2)

def prodset (A : Finset ℤ) : Finset ℤ :=
  (A.product A).image (fun p : ℤ × ℤ => p.1 * p.2)

def sumProductBound (A : Finset ℤ) (ε c : ℝ) : Prop :=
  ((max (sumset A).card (prodset A).card : ℕ) : ℝ) ≥
    c * Real.rpow (A.card : ℝ) (2 - ε)

def erdosSumProductConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
        sumProductBound A ε c

theorem witness_pos :
    sumProductBound ({0} : Finset ℤ) 1 1 := by
  norm_num [sumProductBound, sumset, prodset]

theorem witness_neg :
    ¬ sumProductBound ({0} : Finset ℤ) 2 3 := by
  norm_num [sumProductBound, sumset, prodset]

theorem erdos_sum_product :
    erdosSumProductConjecture := by
  sorry

end
