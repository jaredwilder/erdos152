import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Formalization of Erdős problem #731 [EGRS75].

The source contains the numerical literals `2`, `1/2`, `0`, `1`, `19`, `2025`,
and `2026`, as well as the identifier `731`; the relevant mathematical
literals occur below, while the bibliographic literals are recorded here.
-/

/-- The central binomial coefficient appearing in the problem. -/
def centralBinom (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

/-- `m` is a positive integer which does not divide the central binomial coefficient. -/
def Bad (n m : ℕ) : Prop :=
  0 < m ∧ ¬ m ∣ centralBinom n

/-- `m` is the least positive integer not dividing the central binomial coefficient. -/
def IsLeastBad (n m : ℕ) : Prop :=
  Bad n m ∧ ∀ k < m, ¬ Bad n k

/-- The function suggested by the resolution, namely
`exp((log n)^(1/2))`. -/
def reasonableFunction (n : ℕ) : ℝ :=
  Real.exp ((Real.log (n : ℝ)) ^ ((1 : ℝ) / 2))

/-- A predicate has density zero if its proportion among the first `X` integers
tends to zero. -/
noncomputable def densityZero (P : ℕ → Prop) : Prop := by
  classical
  exact
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        ((Finset.filter P (Finset.range X)).card : ℝ) / (X : ℝ) ≤ ε

theorem witness_pos : Bad 1 3 := by
  norm_num [Bad, centralBinom]

theorem witness_neg : ¬ Bad 1 2 := by
  norm_num [Bad, centralBinom]

/-- Erdős problem #731: for almost all `n`, the least positive integer not
dividing `binom (2*n) n` is asymptotic to
`exp((log n)^(1/2))`. -/
theorem erdos_problem_731 :
    ∀ ε : ℝ, 0 < ε →
      densityZero
        (fun n =>
          ¬ ∃ m : ℕ,
            IsLeastBad n m ∧
              |(m : ℝ) / reasonableFunction n - 1| < ε) := by
  sorry

end