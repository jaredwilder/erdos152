import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    n / 2
  else
    (3 * n + 1) / 2

def iterate : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterate k (collatzStep n)

def hitsOneBy (m k : ℕ) : Prop :=
  1 ≤ k ∧ iterate k m = 1

theorem witness_pos : hitsOneBy 1 2 := by
  norm_num [hitsOneBy, iterate, collatzStep]

theorem witness_neg : ¬ hitsOneBy 0 2 := by
  norm_num [hitsOneBy, iterate, collatzStep]

theorem collatz_conjecture :
    ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, hitsOneBy m k := by
  sorry

end