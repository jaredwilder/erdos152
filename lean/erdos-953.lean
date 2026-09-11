import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Pow.Real


noncomputable section
open scoped BigOperators
open scoped Classical
open Set
open MeasureTheory

def euclideanDistance (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

def Admissible (r : ℝ) (A : Set (ℝ × ℝ)) : Prop :=
  MeasurableSet A ∧
    (∀ x ∈ A, euclideanDistance x (0, 0) < r) ∧
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∀ n : ℤ, euclideanDistance x y ≠ (n : ℝ))

def extremalMeasure (r : ℝ) : ℝ :=
  sSup {m : ℝ | ∃ A : Set (ℝ × ℝ), Admissible r A ∧ ENNReal.toReal (volume A) = m}

theorem witness_pos : Admissible 1 (∅ : Set (ℝ × ℝ)) := by
  simp [Admissible]

theorem witness_neg :
    ¬ Admissible 2 ({(0, 0), (1, 0)} : Set (ℝ × ℝ)) := by
  intro h
  have hn :=
    h.2.2 (0, 0) (by simp) (1, 0) (by simp) (by norm_num) 1
  norm_num [euclideanDistance] at hn

theorem erdos_problem_953 :
    ∃ C : ℝ, 0 < C ∧
      (∀ r : ℝ, 1 ≤ r → extremalMeasure r ≤ C * r) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ c : ℝ, 0 < c ∧
          ∀ r : ℝ, 1 ≤ r →
            c * Real.rpow r (1 / 2 - ε) ≤ extremalMeasure r) := by
  sorry

end