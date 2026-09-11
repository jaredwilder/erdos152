import Mathlib


noncomputable section
open scoped BigOperators
/-!
A decidable encoding of subsets of `ℕ` is given by predicates `ℕ → Bool`.
Representations are counted as unordered pairs, so that a representation
`a + b` is counted only when `a ≤ b`.
-/

/-- The elements of `A` which can participate in a representation of `n`. -/
def trunc (A : ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun a => A a = true)

/-- The number of unordered representations of `n` as a sum of two elements of `A`. -/
def representationCount (A : ℕ → Bool) (n : ℕ) : ℕ :=
  ((trunc A n).product (trunc A n)).filter
    (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card

/-- Membership in the set `B` of integers having exactly one representation. -/
def isUniqueSum (A : ℕ → Bool) (n : ℕ) : Prop :=
  representationCount A n = 1

/-- The number of integers in `{1, ..., N}` which are not unique sums. -/
def missingCount (A : ℕ → Bool) (N : ℕ) : ℕ :=
  letI : DecidablePred (fun n => ¬ isUniqueSum A n) :=
    fun n => by
      unfold isUniqueSum
      infer_instance
  (Finset.Icc 1 N).filter (fun n => ¬ isUniqueSum A n) |>.card

/-- A finite lower-bound predicate for the counting function in the problem. -/
def atLeast (A : ℕ → Bool) (N k : ℕ) : Prop :=
  k ≤ missingCount A N

/-- The assertion that the `N^(1/2-ε)` lower bound holds for a fixed set `A`. -/
def lowerAsymptotic (A : ℕ → Bool) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * Real.rpow (N : ℝ) (1 / 2 - ε) ≤ (missingCount A N : ℝ)

/-- The assertion that the exceptional set is `o(N^(1/2))`. -/
def smallAsymptotic (A : ℕ → Bool) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (missingCount A N : ℝ) ≤ ε * Real.rpow (N : ℝ) (1 / 2)

/-- The two questions posed in Erdős problem 14. -/
def erdosProblem14 : Prop :=
  (∀ A : ℕ → Bool, lowerAsymptotic A) ∧
    (∃ A : ℕ → Bool, smallAsymptotic A)

/-- Source constants `1`, `2`, and `3` also occur in the finite encoding above. -/
def sourceExponentHalf : ℝ := (1 : ℝ) / 2

/-- The exponents `1/3` and `3/2` appearing in the reported resolution. -/
def sourceExponentThird : ℝ := (1 : ℝ) / 3
def sourceExponentThreeHalves : ℝ := (3 : ℝ) / 2

/-- A concrete instance where the finite lower-bound predicate holds. -/
theorem witness_pos :
    atLeast (fun _ : ℕ => false) 1 1 := by
  unfold atLeast
  decide

/-- A concrete instance where the finite lower-bound predicate fails. -/
theorem witness_neg :
    ¬ atLeast (fun n : ℕ => n = 0 ∨ n = 1) 1 1 := by
  unfold atLeast
  decide

/-- Formal statement of the open problem. -/
theorem erdos_problem_14 : erdosProblem14 := by
  sorry

end