import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- The first representation from Erdős problem 1065.
The variables `k` and `q` are natural numbers; in particular, the
natural-number binder for `k` encodes the source condition `k ≥ 0`. -/
def primeForm1 (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k q : ℕ, Nat.Prime q ∧ p = 2 ^ k * q + 1

/-- The second representation from Erdős problem 1065.
The variables `k` and `l` are natural numbers, encoding the
nonnegativity conditions on the exponents. -/
def primeForm2 (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k l q : ℕ, Nat.Prime q ∧ p = 2 ^ k * 3 ^ l * q + 1

/-- A predicate holds for infinitely many natural numbers when it is unbounded. -/
def InfinitelyMany (P : ℕ → Prop) : Prop :=
  ∀ B : ℕ, ∃ p : ℕ, B < p ∧ P p

theorem witness_pos : primeForm1 3 := by
  refine ⟨by norm_num, 0, 2, by norm_num, by norm_num⟩

theorem witness_neg : ¬ primeForm1 2 := by
  intro h
  rcases h with ⟨_, k, q, hq, heq⟩
  have hq' : 2 ≤ q := hq.two_le
  have hpow : 1 ≤ 2 ^ k := by
    have hpow' : 0 < 2 ^ k := by positivity
    omega
  have hprod : 2 ≤ 2 ^ k * q := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ 2 ^ k * q := Nat.mul_le_mul hpow hq'
  omega

/-- The open alternative posed in Erdős problem 1065. -/
theorem erdos_1065 :
    InfinitelyMany primeForm1 ∨ InfinitelyMany primeForm2 := by
  sorry

end