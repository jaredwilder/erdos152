import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def problemNumber : ℕ := 820

def reportedHValues : List ℕ := [3, 3, 3, 6, 3, 18, 3, 6, 3, 12]

def CoprimePowerPair (n k l : ℕ) : Prop :=
  1 < k ∧ k < l ∧ Nat.gcd (k ^ n - 1) (l ^ n - 1) = 1

def Good (n : ℕ) : Prop :=
  Nat.gcd (2 ^ n - 1) (3 ^ n - 1) = 1

noncomputable def H (n : ℕ) : ℕ :=
  sInf {l : ℕ | ∃ k : ℕ, CoprimePowerPair n k l}

noncomputable def K (n : ℕ) : ℕ :=
  sInf {k : ℕ | 2 < k ∧ Nat.gcd (k ^ n - 1) (2 ^ n - 1) = 1}

def UnboundedlyOften (P : ℕ → Prop) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n

def LowerBoundClaim (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    UnboundedlyOften
      (fun n =>
        (H n : ℝ) >
          Real.exp
            (Real.rpow (n : ℝ)
              ((c - ε) / Real.log (Real.log (n : ℝ)))))

def UpperBoundClaim (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (H n : ℝ) <
        Real.exp
          (Real.rpow (n : ℝ)
            ((c + ε) / Real.log (Real.log (n : ℝ))))

def KUpperBoundClaim (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (K n : ℝ) <
        Real.exp
          (Real.rpow (n : ℝ)
            ((c + ε) / Real.log (Real.log (n : ℝ))))

def ErdosProblem820 : Prop :=
  UnboundedlyOften Good ∧
    ∃ c : ℝ, 0 < c ∧
      LowerBoundClaim c ∧
      UpperBoundClaim c ∧
      KUpperBoundClaim c

theorem witness_pos : Good 1 := by
  norm_num [Good]

theorem witness_neg : ¬ Good 4 := by
  norm_num [Good]

theorem erdos_problem_820 : ErdosProblem820 := by
  sorry

end