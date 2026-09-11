import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/--
A finite set of natural numbers represents the uniquely increasing list of its
elements.  Thus this predicate expresses the distinctness and ordering
conditions in the question without introducing tuples.
-/
def IsUnitFractionSolution (k : ℕ) (s : Finset ℕ) : Prop :=
  s.card = k ∧
    (∀ n ∈ s, 1 ≤ n) ∧
    (Finset.sum s (fun n => (1 : ℚ) / n)) = 1

def SolutionFamily (k : ℕ) : Set (Finset ℕ) :=
  {s | IsUnitFractionSolution k s}

/-- The number of solutions, represented as the cardinality of the solution family. -/
noncomputable def F (k : ℕ) : ℕ :=
  Set.ncard (SolutionFamily k)

/-- The Vardi constant appearing in the known upper estimate. -/
def vardiConstant : ℝ := 1.26408

theorem witness_pos :
    IsUnitFractionSolution 1 ({1} : Finset ℕ) := by
  norm_num [IsUnitFractionSolution]

theorem witness_neg :
    ¬ IsUnitFractionSolution 1 ({2} : Finset ℕ) := by
  norm_num [IsUnitFractionSolution]

/--
The known form of the estimates for the number of representations by distinct
unit fractions: for some absolute positive constant `c`, the lower bound has
the shape `2^(c^(k / log k))`, while the upper bound has the Vardi constant
with exponent `(1/5 + o(1)) * 2^k`.
-/
theorem erdos_problem_148_estimates :
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ k : ℕ in Filter.atTop,
          Real.rpow (2 : ℝ)
              (Real.rpow c ((k : ℝ) / Real.log (k : ℝ))) ≤
              (F k : ℝ) ∧
            (F k : ℝ) ≤
              Real.rpow vardiConstant
                (((1 : ℝ) / 5 + ε) * (2 : ℝ) ^ k) := by
  sorry

end