import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem #479.

Question:
Is it true that, for all k ≠ 1, there are infinitely many n such that
2^n ≡ k mod n?

Resolution notes:
#479 : [ErGr80,p.96] number theory A conjecture of Graham. It is easy to see
that 2^n ≠ 1 mod n for all n>1, so the restriction k≠1 is necessary.
Erdős and Graham report that Graham, Lehmer, and Lehmer have proved this
for k=2^i for i≥1, or if k=-1. When k=3 the smallest n such that
2^n ≡ 3 mod n is n=4700063497. The minimal such n for each k is
A036236. Additional references include A015919, A050259, A015921,
A006521, A006517, and A015940. The source page was edited 03 December
2025 and accessed 2026-08-30.
-/

/-- The congruence appearing in Erdős problem #479. -/
def congruentPower (k : ℤ) (n : ℕ) : Prop :=
  Int.ModEq (n : ℤ) (2 ^ n) k

/-- The phrase "infinitely many n" expressed as unboundedness in ℕ. -/
def infinitelyOften (k : ℤ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ congruentPower k n

theorem witness_pos : congruentPower 2 2 := by
  norm_num [congruentPower, Int.ModEq]

theorem witness_neg : ¬ congruentPower 3 3 := by
  norm_num [congruentPower, Int.ModEq]

/-- Erdős problem #479, as stated in the source. -/
theorem erdos_problem_479 :
    ∀ k : ℤ, k ≠ 1 → infinitelyOften k := by
  sorry

end