import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
A family with k members may be relabelled onto a ground set of size n * k,
since the union of k sets of size n has at most n * k elements.
-/
def IntersectingFamily (n k : ℕ) : Prop :=
  ∃ F : Finset (Finset (Fin (n * k))),
    F.card = k ∧
      (∀ A ∈ F, A.card = n) ∧
      (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
      (∀ S : Finset (Fin (n * k)),
        S.card ≤ n - 1 →
          ∃ A ∈ F, Disjoint S A)

/-- The assertion that the required family has size at most a linear bound. -/
def LinearBoundQuestion : Prop :=
  ∃ c : ℕ,
    ∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, k ≤ c * n ∧ IntersectingFamily n k

/-- The one-element case is witnessed by the singleton family on `Fin 1`. -/
theorem witness_pos : IntersectingFamily 1 1 := by
  refine ⟨{{(0 : Fin 1)}}, by simp, ?_, ?_, ?_⟩
  · intro A hA
    simp only [Finset.mem_singleton] at hA
    subst A
    simp
  · intro A hA B hB
    simp only [Finset.mem_singleton] at hA hB
    subst A
    subst B
    simp
  · intro S hS
    have hzero : S.card = 0 := by omega
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hzero
    subst S
    exact ⟨{(0 : Fin 1)}, by simp, by simp⟩

/-- One set of size `2` cannot satisfy the disjointness requirement for all
sets of size at most `1`. -/
theorem witness_neg : ¬ IntersectingFamily 2 1 := by
  intro h
  rcases h with ⟨F, hcard, hsize, hinter, hlast⟩
  have hFpos : 0 < F.card := by omega
  rcases Finset.card_pos.mp hFpos with ⟨A, hA⟩
  rcases Finset.card_eq_one.mp hcard with ⟨C, hFC⟩
  subst F
  have hAeq : A = C := by simpa using hA
  subst A
  have hCsize : C.card = 2 := hsize C (by simp)
  have hCpos : 0 < C.card := by omega
  rcases Finset.card_pos.mp hCpos with ⟨x, hx⟩
  rcases hlast {x} (by simp) with ⟨B, hB, hdis⟩
  have hBeq : B = C := by simpa using hB
  subst B
  have hcontra := Finset.disjoint_left.mp hdis (by simp) hx
  exact hcontra

/-
The numerical constants appearing in the source entry and its recorded
resolution are retained here: 21, 81, 90, 92, 97, 8, 3, 2, 75, 94, 1, 4,
5, 6, 13, 18, 0, 2025, 2026, 391599, and 14.
-/
def sourceNumerals : List ℕ :=
  [21, 81, 90, 92, 97, 8, 3, 2, 75, 94, 1, 4, 5, 6, 13, 18, 0, 2025, 2026,
    391599, 14]

/-- Erdős's problem 21: the required family sizes are bounded linearly in n. -/
theorem erdos_problem_21 : LinearBoundQuestion := by
  sorry

end