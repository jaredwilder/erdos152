import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter

/-
Source numeric literals: 32, 56, 132, 57, 295, 59, 117, 61, 229, 65, 227,
73, 133, 77, 62, 99, 1, 9, 54, 96, 98, 50, 04, 2026, 08, 30, 0, 2,
and 1.781.
-/

/-- The number of elements of `A` in `{1, ..., N}`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

/-- Every sufficiently large natural number is a prime plus an element of `A`. -/
def IsAdditiveComplementToPrimes (A : Set ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ p a : ℕ, Nat.Prime p ∧ a ∈ A ∧ n = p + a

/-- The `o((log N)^2)` condition. -/
def SmallOLogSq (A : Set ℕ) : Prop :=
  Tendsto
    (fun N : ℕ =>
      (countUpTo A N : ℝ) / (Real.log (N : ℝ)) ^ 2)
    atTop (𝓝 0)

/-- The `O(log N)` condition. -/
def BigOLog (A : Set ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ N : ℕ in atTop,
      (countUpTo A N : ℝ) ≤ C * Real.log (N : ℝ)

/-- The lower-bound assertion involving Euler's constant. -/
def HasRequiredLowerBound (A : Set ℕ) : Prop :=
  Filter.liminf
      (fun N : ℕ =>
        (countUpTo A N : ℝ) / Real.log (N : ℝ))
      atTop ≥ Real.exp Real.eulerMascheroniConstant

/--
A finite, decidable approximation to being an additive complement: every
integer from `2` through `N` is a prime plus an element of the finite set.
-/
def FiniteAdditiveCover (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ Finset.Icc 2 N,
    ∃ p ∈ Finset.Icc 2 n, Nat.Prime p ∧
      ∃ a ∈ A, n = p + a

theorem witness_pos :
    FiniteAdditiveCover ({0} : Finset ℕ) 2 := by
  unfold FiniteAdditiveCover
  intro n hn
  have hn2 : n = 2 := by
    simp only [Finset.mem_Icc] at hn
    omega
  subst n
  refine ⟨2, ?_, Nat.prime_two, 0, ?_, ?_⟩
  · simp
  · simp
  · norm_num

theorem witness_neg :
    ¬ FiniteAdditiveCover (∅ : Finset ℕ) 2 := by
  unfold FiniteAdditiveCover
  intro h
  obtain ⟨p, hp, hprime, a, ha, heq⟩ := h 2 (by simp)
  simpa using ha

/--
Erdős problem 32: existence of an additive complement to the primes with
subquadratic logarithmic counting function, the possibility of a logarithmic
bound, and the asserted necessary lower bound.
-/
theorem erdos_problem_32 :
    (∃ A : Set ℕ,
      SmallOLogSq A ∧ IsAdditiveComplementToPrimes A) ∧
    (∃ A : Set ℕ,
      BigOLog A ∧ IsAdditiveComplementToPrimes A) ∧
    (∀ A : Set ℕ,
      IsAdditiveComplementToPrimes A → HasRequiredLowerBound A) := by
  sorry

end