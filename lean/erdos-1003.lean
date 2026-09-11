import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  Erdos Problem 1003.

  The source asks whether there are infinitely many solutions to
  φ(n) = φ(n + 1), and also records the stronger conjecture for every k ≥ 1.
  Its additional references include Er85e, EPS87, 946, and 415, together
  with the bounds involving 1/3.  The source metadata also mentions 0 proof
  expositions, 5 comments, and dates 19 April 2026 and 2026-08-30.
-/

def IsTotientPair (n : ℕ) : Prop :=
  Nat.totient n = Nat.totient (n + 1)

theorem witness_pos : IsTotientPair 1 := by
  change Nat.totient 1 = Nat.totient 2
  rw [Nat.totient_one]
  simpa using (Nat.totient_prime (by norm_num : Nat.Prime 2)).symm

theorem witness_neg : ¬ IsTotientPair 2 := by
  change ¬ (Nat.totient 2 = Nat.totient 3)
  intro h
  have h2 : Nat.totient 2 = 1 := by
    simpa using (Nat.totient_prime (by norm_num : Nat.Prime 2))
  have h3 : Nat.totient 3 = 2 := by
    simpa using (Nat.totient_prime (by norm_num : Nat.Prime 3))
  rw [h2, h3] at h
  norm_num at h

/--
There are infinitely many natural numbers `n` satisfying
`φ(n) = φ(n + 1)`, expressed as the existence of such an `n`
above every natural bound.
-/
theorem infinitely_many_totient_pairs :
    ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ IsTotientPair n := by
  sorry

end