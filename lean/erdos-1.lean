import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

def subsetSum (N : ℕ) (S : Finset (Fin N)) : ℕ :=
  S.sum (fun x => x.val + 1)

def subsetSumsDistinct (N : ℕ) (A : Finset (Fin N)) : Prop :=
  ∀ S ∈ A.powerset, ∀ T ∈ A.powerset,
    subsetSum N S = subsetSum N T → S = T

def hasDistinctSubsetSums (N n : ℕ) : Prop :=
  ∃ A : Finset (Fin N),
    A.card = n ∧ subsetSumsDistinct N A

def erdosProblem1 : Prop :=
  ∃ c : ℚ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ N, hasDistinctSubsetSums N n →
      c * (2 : ℚ) ^ n ≤ (N : ℚ)

theorem witness_pos : hasDistinctSubsetSums 1 1 := by
  refine ⟨{0}, by simp, ?_⟩
  intro S _ T _ hEq
  by_cases hs : (0 : Fin 1) ∈ S
  · have hS : S = {0} := by
      ext x
      have hx : x = (0 : Fin 1) := Fin.eq_zero x
      subst x
      simp [hs]
    by_cases ht : (0 : Fin 1) ∈ T
    · have hT : T = {0} := by
        ext x
        have hx : x = (0 : Fin 1) := Fin.eq_zero x
        subst x
        simp [ht]
      exact hS.trans hT.symm
    · have hT : T = ∅ := by
        ext x
        have hx : x = (0 : Fin 1) := Fin.eq_zero x
        subst x
        simp [ht]
      exfalso
      simpa [hS, hT, subsetSum] using hEq
  · have hS : S = ∅ := by
      ext x
      have hx : x = (0 : Fin 1) := Fin.eq_zero x
      subst x
      simp [hs]
    by_cases ht : (0 : Fin 1) ∈ T
    · have hT : T = {0} := by
        ext x
        have hx : x = (0 : Fin 1) := Fin.eq_zero x
        subst x
        simp [ht]
      exfalso
      simpa [hS, hT, subsetSum] using hEq
    · have hT : T = ∅ := by
        ext x
        have hx : x = (0 : Fin 1) := Fin.eq_zero x
        subst x
        simp [ht]
      exact hS.trans hT.symm

theorem witness_neg : ¬ hasDistinctSubsetSums 1 2 := by
  intro h
  rcases h with ⟨A, hA, _⟩
  have hle : A.card ≤ (Finset.univ : Finset (Fin 1)).card :=
    Finset.card_le_card (Finset.subset_univ A)
  have hle' : A.card ≤ 1 := by
    simpa using hle
  omega

theorem erdos_problem_1 : erdosProblem1 := by
  sorry

end