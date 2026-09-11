import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- A finite set is non-averaging when no member is the average of
    at least two distinct other members. -/
def nonAveraging (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, ∀ B ∈ A.powerset, n ∉ B → 2 ≤ B.card →
    B.sum id ≠ B.card * n

/-- The maximal size of a non-averaging subset of `{1, ..., N}`. -/
noncomputable def F (N : ℕ) : ℕ :=
  by
    classical
    exact
      ((Finset.Icc 1 N).powerset.filter (fun A => nonAveraging A)).sup
        Finset.card

theorem witness_pos : nonAveraging ({1, 3} : Finset ℕ) := by
  rw [nonAveraging]
  intro n hn B hB hnB hcard
  have hsub : B ⊆ ({1, 3} : Finset ℕ) :=
    Finset.mem_powerset.mp hB
  have hcard' : ({1, 3} : Finset ℕ).card ≤ B.card := by
    simpa using hcard
  have heq : B = ({1, 3} : Finset ℕ) :=
    Finset.eq_of_subset_of_card_le hsub hcard'
  exfalso
  apply hnB
  rw [heq]
  exact hn

theorem witness_neg : ¬ nonAveraging ({1, 2, 3} : Finset ℕ) := by
  intro h
  rw [nonAveraging] at h
  have hbad :=
    h 2 (by simp) ({1, 3} : Finset ℕ) (by simp) (by simp) (by norm_num)
  apply hbad
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- The known order-of-growth bounds for Erdos problem 186:
    `N^(1/4) ≪ F(N) ≪ N^(1/4+o(1))`. -/
def growthClaim : Prop :=
  (∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      c * Real.rpow (N : ℝ) (1 / 4 : ℝ) ≤ (F N : ℝ)) ∧
  (∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (F N : ℝ) ≤ C * Real.rpow (N : ℝ) (1 / 4 + ε))

theorem erdos_problem_186 : growthClaim := by
  sorry

end