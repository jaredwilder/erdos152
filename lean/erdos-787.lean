import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Erdős problem #787.  The original statement is over finite subsets of ℝ.
Following the resolution, we use finite subsets of ℤ, since Choi observed
that this entails no loss of generality.

Source numerals and references: #787, Er65, p.187, Er73, p.130, Va99, 1.22,
n^{2/5+o(1)}, Sa21, Ru05, Be25, 1+1/68+o(1), 23 January 2026,
2026-08-30.
-/

/-- A finite set `B` is admissible inside `A` when distinct elements of `B`
do not have their sum in `A`. -/
def GoodSubset (A B : Finset ℤ) : Prop :=
  B ⊆ A ∧ (B : Set ℤ).Pairwise (fun x y => x + y ∉ A)

/-- There is an admissible subset of `A` having at least `k` elements. -/
def HasGood (A : Finset ℤ) (k : ℕ) : Prop :=
  (A.powerset.filter (fun B => GoodSubset A B ∧ k ≤ B.card)).Nonempty

/-- Every `n`-element finite integer set has an admissible subset of size
at least `k`. -/
def Guarantees (n k : ℕ) : Prop :=
  ∀ A : Finset ℤ, A.card = n → HasGood A k

/-- The finite-set version of the extremal function in the problem. -/
noncomputable def g (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => Guarantees n k) n

theorem witness_pos : HasGood ({1, 2} : Finset ℤ) 1 := by
  rw [HasGood]
  refine ⟨{1}, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · constructor
    · simp [GoodSubset, Set.Pairwise]
    · simp

theorem witness_neg : ¬ HasGood ({0, 1, 2} : Finset ℤ) 3 := by
  rw [HasGood]
  rintro ⟨B, hB⟩
  rcases Finset.mem_filter.mp hB with ⟨hpow, hcond⟩
  have hsub : B ⊆ ({0, 1, 2} : Finset ℤ) :=
    Finset.mem_powerset.mp hpow
  have hEq : B = ({0, 1, 2} : Finset ℤ) :=
    Finset.eq_of_subset_of_card_le hsub (by
      simpa using hcond.2)
  have hp :
      (({0, 1, 2} : Finset ℤ) : Set ℤ).Pairwise
        (fun x y => x + y ∉ ({0, 1, 2} : Finset ℤ)) := by
    simpa only [hEq] using hcond.1.2
  have hbad : (0 : ℤ) + 1 ∉ ({0, 1, 2} : Finset ℤ) :=
    hp (by simp) (by simp) (by norm_num)
  exact hbad (by simp)

/-
The resolution records the currently known estimates
  (log n)^(1+c) ≪ g(n) ≪ exp(sqrt(log n))
for some c > 0, with the lower bound due to Sanders and the upper bound
due to Ruzsa.  Beker's later lower bound is
  (log n)^(1+1/68+o(1)) ≪ g(n).
-/
theorem resolution_bounds :
    ∃ c C D : ℝ,
      0 < c ∧ 0 < C ∧ 0 < D ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        C * Real.rpow (Real.log (n : ℝ)) (1 + c) ≤ (g n : ℝ)) ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        (g n : ℝ) ≤
          D * Real.exp (Real.sqrt (Real.log (n : ℝ)))) := by
  sorry

end