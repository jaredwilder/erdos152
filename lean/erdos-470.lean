import Mathlib


section
open scoped BigOperators
def divisors (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun d => d ∣ n)

def properDivisors (n : ℕ) : Finset ℕ :=
  (divisors n).filter (fun d => d < n)

def sigma (n : ℕ) : ℕ :=
  (divisors n).sum id

def pseudoperfect (n : ℕ) : Prop :=
  ((properDivisors n).powerset.filter (fun s => s.sum id = n)).Nonempty

def weird (n : ℕ) : Prop :=
  0 < n ∧ sigma n ≥ 2 * n ∧ ¬ pseudoperfect n

instance weirdDecidable (n : ℕ) : Decidable (weird n) := by
  unfold weird pseudoperfect
  infer_instance

def oddWeirdExists : Prop :=
  ∃ n : ℕ, n % 2 = 1 ∧ weird n

def primitiveWeird (n : ℕ) : Prop :=
  weird n ∧
    (divisors n).filter (fun d => d < n ∧ weird d) = ∅

def infinitelyManyPrimitiveWeird : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B < n ∧ primitiveWeird n

def sourceProblemNumber : ℕ := 470
def sourceSmallestWeird : ℕ := 70
def sourceSigmaFactor : ℕ := 2
def sourceGapNumerator : ℚ := 1
def sourceGapDenominator : ℚ := 10
def sourceGapExponent : ℚ := 1 / 2
def sourceComputationalBound : ℕ := 10 ^ 21
def sourcePrimeDivisorLowerBound : ℕ := 6
def sourceAbundancyBound : ℕ := 4
def sourceRelatedProblem : ℕ := 825
def sourceBounty : ℕ := 10

theorem witness_pos : weird 70 := by
  decide

theorem witness_neg : ¬ weird 1 := by
  decide

theorem erdos_problem_470 :
    ¬ oddWeirdExists ∧ infinitelyManyPrimitiveWeird := by
  sorry

end