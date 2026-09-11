import Mathlib


noncomputable section
open scoped BigOperators
/-
For fixed `k` and `x`, the condition that every member of
`n + 1, ..., n + k` has a prime divisor at most `x` is periodic modulo
`(x + 1)!`.  Thus the existence of a positive-density set is represented
by the existence of one residue in the finite range below `(x + 1)!`.
-/

def covered (k x n : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 k,
    ∃ p ∈ Finset.Icc 2 x, Nat.Prime p ∧ p ∣ (n + i)

def coverable (k x : ℕ) : Prop :=
  ∃ n ∈ Finset.range (Nat.factorial (x + 1)), covered k x n

def minimalThreshold (k x : ℕ) : Prop :=
  coverable k x ∧
    ∀ y ∈ Finset.range x, ¬ coverable k y

/-- The exponent `1/2` occurring in the recorded Rosser-sieve bound. -/
def rosserExponent : ℝ := 1 / 2

/-- The index `k + 1` used in the elementary upper-bound construction. -/
def elementaryUpperIndex (k : ℕ) : ℕ := k + 1

theorem witness_pos : coverable 2 3 := by
  unfold coverable
  refine ⟨1, by norm_num [Nat.factorial], ?_⟩
  unfold covered
  intro i hi
  have hi' : 1 ≤ i ∧ i ≤ 2 := by
    simpa [Finset.mem_Icc] using hi
  rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩

theorem witness_neg : ¬ coverable 2 2 := by
  intro h
  unfold coverable at h
  rcases h with ⟨n, _hn, hc⟩
  have h1 := hc 1 (by norm_num)
  have h2 := hc 2 (by norm_num)
  rcases h1 with ⟨p1, hp1, _hprime1, hdiv1⟩
  rcases h2 with ⟨p2, hp2, _hprime2, hdiv2⟩
  have hp1eq : p1 = 2 := by
    simp [Finset.mem_Icc] at hp1
    omega
  have hp2eq : p2 = 2 := by
    simp [Finset.mem_Icc] at hp2
    omega
  subst p1
  subst p2
  rcases hdiv1 with ⟨q1, hq1⟩
  rcases hdiv2 with ⟨q2, hq2⟩
  omega

/-
The open assertion that the least threshold satisfies
`S(k) ≥ k^(1-o(1))`, expressed in the usual epsilon formulation.
-/
theorem conjectured_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        ∀ x : ℕ, minimalThreshold k x →
          Real.rpow (k : ℝ) (1 - ε) ≤ (x : ℝ) := by
  sorry

end