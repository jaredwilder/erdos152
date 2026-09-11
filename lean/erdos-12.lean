import Mathlib


noncomputable section
open scoped BigOperators
open scoped BigOperators
open Filter

/-- The finite, decidable version of the forbidden-divisibility condition. -/
def GoodFinset (A : Finset ℕ) : Prop :=
  A.attach.filter (fun a =>
    A.attach.filter (fun b =>
      A.attach.filter (fun c =>
        ¬ (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1 ∧
          a.1 ∣ b.1 + c.1 ∧ b.1 > a.1 ∧ c.1 > a.1)) = A.attach) = A.attach) = A.attach

theorem witness_pos : GoodFinset ({1, 2} : Finset ℕ) := by
  unfold GoodFinset
  decide

theorem witness_neg : ¬ GoodFinset ({1, 2, 4} : Finset ℕ) := by
  unfold GoodFinset
  decide

/-- The forbidden-divisibility condition for an infinite set of positive integers. -/
def GoodSet (A : Set ℕ) : Prop :=
  0 ∉ A ∧
    ∀ ⦃a b c : ℕ⦄,
      a ∈ A →
      b ∈ A →
      c ∈ A →
      a ≠ b →
      a ≠ c →
      b ≠ c →
      a ∣ b + c →
      b > a →
      c > a →
      False

/-- Positive lower liminf after normalization by `N^(1/2)`. -/
def HasPositiveSqrtLowerDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
      ∀ᶠ N : ℕ in atTop,
        δ ≤
          ((A ∩ Set.Icc 1 N).ncard : ℝ) /
            Real.rpow (N : ℝ) ((1 : ℝ) / 2)

/-- The assertion that the second question has a positive answer. -/
def HasPowerSaving (A : Set ℕ) : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      Set.Infinite
        {N : ℕ |
          ((A ∩ Set.Icc 1 N).ncard : ℝ) <
            Real.rpow (N : ℝ) (1 - c)}

/-- The reciprocal series over a set of natural numbers. -/
noncomputable def ReciprocalSeries (A : Set ℕ) : ℕ → ℝ :=
  by
    classical
    exact fun n => if n ∈ A then (1 : ℝ) / (n : ℝ) else 0

def ErdosQuestion12First : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ GoodSet A ∧ HasPositiveSqrtLowerDensity A

def ErdosQuestion12Second : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      ∀ A : Set ℕ,
        A.Infinite →
        GoodSet A →
        Set.Infinite
          {N : ℕ |
            ((A ∩ Set.Icc 1 N).ncard : ℝ) <
              Real.rpow (N : ℝ) (1 - c)}

def ErdosQuestion12Third : Prop :=
  ∀ A : Set ℕ, A.Infinite → GoodSet A → Summable (ReciprocalSeries A)

/-- Erdős problem 12: the first question is affirmative, the second is negative,
and the reciprocal-series question asks whether this always converges. -/
def ErdosProblem12 : Prop :=
  ErdosQuestion12First ∧ ¬ ErdosQuestion12Second ∧ ErdosQuestion12Third

theorem erdos_problem_12 : ErdosProblem12 := by
  sorry

end