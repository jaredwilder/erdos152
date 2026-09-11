import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem 850.  We interpret “prime factors” for nonzero integers as
the prime factors of their absolute values.
The numerical data appearing in the source includes:
#850, 63, 60, 80, 96, 2, 1, 75, 1215, 3, 5, 76, 19, 1216, 2024,
677, 2011, 19, 04, 0, 343101, 28, 2025, 2026, 30.
-/

def primeFactors (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ n % p = 0)

def samePrimeFactors (a b : ℤ) : Prop :=
  primeFactors a.natAbs = primeFactors b.natAbs

def sameThree (x y : ℤ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧
    x + 1 ≠ 0 ∧ y + 1 ≠ 0 ∧
    x + 2 ≠ 0 ∧ y + 2 ≠ 0 ∧
    samePrimeFactors x y ∧
    samePrimeFactors (x + 1) (y + 1) ∧
    samePrimeFactors (x + 2) (y + 2)

def sourceExampleX : ℤ := 75
def sourceExampleY : ℤ := 1215

theorem witness_pos : sameThree 1 1 := by
  norm_num [sameThree, samePrimeFactors]

theorem witness_neg : ¬ sameThree 1 2 := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, hp, _, _⟩
  have hp' : primeFactors 1 = primeFactors 2 := by
    simpa [samePrimeFactors] using hp
  have hmem : 2 ∈ primeFactors 2 := by
    norm_num [primeFactors]
  have hnot : 2 ∉ primeFactors 1 := by
    norm_num [primeFactors]
  apply hnot
  rw [hp']
  exact hmem

theorem erdos_850 :
    ∃ x y : ℤ, x ≠ y ∧ sameThree x y := by
  sorry

end