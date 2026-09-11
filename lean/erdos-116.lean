import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Card

noncomputable section

open scoped BigOperators ENNReal
open Set
open MeasureTheory

namespace ErdosProblem116

def Polynomial (n : ℕ) (roots : Fin n → ℂ) : ℂ → ℂ :=
  fun z => ∏ i : Fin n, (z - roots i)

def SublevelSet (n : ℕ) (roots : Fin n → ℂ) : Set ℂ :=
  {z : ℂ | ‖Polynomial n roots z‖ < 1}

def SublevelArea (n : ℕ) (roots : Fin n → ℂ) : ℝ≥0∞ :=
  volume (SublevelSet n roots)

def RootsInUnitDisk (n : ℕ) (roots : Fin n → ℂ) : Prop :=
  ∀ i, ‖roots i‖ ≤ 1

/-- The assertion that the sublevel set has a polynomially large area. -/
def PolynomialLowerBound : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      ∀ roots : Fin n → ℂ, RootsInUnitDisk n roots →
        ENNReal.ofReal C / (n : ℝ≥0∞) ^ k <
          SublevelArea n roots

/-- The stronger logarithmic lower bound mentioned in the problem. -/
def LogarithmicLowerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ roots : Fin n → ℂ, RootsInUnitDisk n roots →
        ENNReal.ofReal (C / Real.log (n : ℝ)) <
          SublevelArea n roots

/--
Pommerenke's lower bound: uniformly for all monic polynomials whose roots
lie in the closed unit disk, the sublevel set has area at least a constant
times `n⁻⁴`.
-/
axiom pommerenke_lower_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      ∀ roots : Fin n → ℂ, RootsInUnitDisk n roots →
        ENNReal.ofReal C / (n : ℝ≥0∞) ^ 4 <
          SublevelArea n roots

/--
The logarithmic lower bound proved by Krishnapur, Lundberg, and Ramachandran.
-/
axiom krishnapur_lundberg_ramachandran_lower_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ roots : Fin n → ℂ, RootsInUnitDisk n roots →
        ENNReal.ofReal (C / Real.log (n : ℝ)) <
          SublevelArea n roots

/-- Pólya's universal upper bound. -/
axiom polya_upper_bound :
  ∀ n : ℕ, ∀ roots : Fin n → ℂ, RootsInUnitDisk n roots →
    SublevelArea n roots ≤ ENNReal.ofReal Real.pi

/-- Equality in Pólya's bound occurs precisely for identical roots. -/
axiom polya_equality_characterization :
  ∀ n : ℕ, 1 ≤ n →
    ∀ roots : Fin n → ℂ, RootsInUnitDisk n roots →
      SublevelArea n roots = ENNReal.ofReal Real.pi ↔
        ∃ a : ℂ, ∀ i, roots i = a

theorem polynomial_lower_bound : PolynomialLowerBound := by
  obtain ⟨C, hC, h⟩ := pommerenke_lower_bound
  refine ⟨C, 4, hC, ?_⟩
  intro n hn roots hroots
  exact h n hn roots hroots

theorem logarithmic_lower_bound : LogarithmicLowerBound :=
  krishnapur_lundberg_ramachandran_lower_bound

theorem answer_to_erdos_problem_116 :
    PolynomialLowerBound ∧ LogarithmicLowerBound := by
  exact ⟨polynomial_lower_bound, logarithmic_lower_bound⟩

end ErdosProblem116