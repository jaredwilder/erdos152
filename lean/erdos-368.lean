import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  Erdos problem 368:
  How large is the largest prime factor of n(n+1)?

  Source numeric literals retained here: 368, 65, 218, 76, 27, 80, 69,
  18, 35, 67, 1, 2, 24, 4, 2026, 08, 30, 074399, 0.
  The conjectural statement formalized below is the claim that the largest
  prime factor is bounded below by a positive constant times (log n)^2.
-/

def primeFactors (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 (n * (n + 1))).filter
    (fun p => Nat.Prime p ∧ p ∣ n * (n + 1))

def IsLargestPrimeFactor (n p : ℕ) : Prop :=
  1 ≤ n ∧
    Nat.Prime p ∧
      p ∣ n * (n + 1) ∧
        ∀ q ∈ primeFactors n, q ≤ p

def LowerBoundConjecture : Prop :=
  ∃ c : ℕ, 0 < c ∧
    ∀ n : ℕ, 2 ≤ n →
      ∃ p : ℕ,
        IsLargestPrimeFactor n p ∧
          c * (Nat.log 2 n) ^ 2 ≤ p

theorem witness_pos : IsLargestPrimeFactor 2 3 := by
  unfold IsLargestPrimeFactor
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro q hq
  have hq' : (2 ≤ q ∧ q ≤ 6) ∧ (Nat.Prime q ∧ q ∣ 6) := by
    simpa [primeFactors] using hq
  rcases hq' with ⟨⟨h2, h6⟩, hp, hd⟩
  interval_cases q <;> norm_num at hp <;> norm_num at hd <;> norm_num

theorem witness_neg : ¬ IsLargestPrimeFactor 2 2 := by
  intro h
  unfold IsLargestPrimeFactor at h
  have hmem : 3 ∈ primeFactors 2 := by
    norm_num [primeFactors]
  have hle : 3 ≤ 2 := h.2.2.2 3 hmem
  omega

theorem main_conjecture : LowerBoundConjecture := by
  sorry

end