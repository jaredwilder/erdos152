import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

def intervalProduct (u v : ℕ) : ℕ :=
  Finset.prod (Finset.Icc u v) (fun m => m)

def largestPrimeRepeated (u v : ℕ) : Prop :=
  1 ≤ u ∧
    u ≤ v ∧
    let P := intervalProduct u v
    ∃ p ∈ Finset.range (P + 1),
      Nat.Prime p ∧
        p ^ 2 ∣ P ∧
          ∀ q ∈ Finset.range (P + 1),
            Nat.Prime q → q ∣ P → q ≤ p

def SubpolynomialGaps : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ u v : ℕ,
      N ≤ v →
        largestPrimeRepeated u v →
          ((v - u : ℕ) : ℝ) ≤ Real.rpow (v : ℝ) ε

def ArbitrarilyLargeGaps : Prop :=
  ∀ K : ℕ, ∃ u v : ℕ,
    largestPrimeRepeated u v ∧ K ≤ v - u

def erdosProblemNumber : ℕ := 382

def sourceReferenceYear : ℕ := 80

def relatedProblemOne : ℕ := 383

def relatedProblemTwo : ℕ := 380

def sourceOeisNumber : ℕ := 388850

def squareRootExponent : ℝ := 1 / 2

theorem witness_pos : largestPrimeRepeated 4 4 := by
  unfold largestPrimeRepeated
  dsimp [intervalProduct]
  refine ⟨by norm_num, by norm_num, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro q hq hprime hqd
  have hqlt : q < 5 := by simpa using hq
  interval_cases q
  · norm_num at hprime
  · norm_num at hprime
  · norm_num
  · norm_num at hqd
  · norm_num at hprime

theorem witness_neg : ¬ largestPrimeRepeated 2 2 := by
  intro h
  dsimp [largestPrimeRepeated, intervalProduct] at h
  rcases h with ⟨_, _, p, hp, hprime, hdiv, _⟩
  have hp' : p < 3 := by simpa using hp
  have hp2 : 2 ≤ p := hprime.two_le
  have : p = 2 := by omega
  subst p
  norm_num at hdiv

theorem erdos_382_conjecture :
    SubpolynomialGaps ∧ ArbitrarilyLargeGaps := by
  sorry

end