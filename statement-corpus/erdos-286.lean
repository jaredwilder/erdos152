/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 2$. Is it true that there exists an interval $I$ of width $(e-1+o(1))k$ and integers $n_1<\cdots<n_k\in I$ such that\[1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#286 : [ErGr80,p.33] number theory | unit fractions The answer is yes, proved by Croot [Cr01] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links This page was last edited 28 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #286, https://www.erdosproblems.com/286, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos286

/-- `FitsInterval n a b` means that every integer represented by `n` lies in the
real interval with endpoints `a` and `b`. -/
def FitsInterval (n : Fin k → ℕ) (a b : ℝ) : Prop :=
  ∀ i, a ≤ (n i : ℝ) ∧ (n i : ℝ) ≤ b

/-- `UnitPacking k n` says that `n` is a strictly increasing list of `k`
positive integers whose reciprocals sum to one. -/
def UnitPacking (k : ℕ) (n : Fin k → ℕ) : Prop :=
  (∀ i, 0 < n i) ∧
    (∀ ⦃i j⦄, i < j → n i < n j) ∧
    (∑ i ∈ Finset.univ, (1 : ℚ) / (n i : ℚ)) = 1

/-- `BoundedUnitPacking k c` asserts the existence of a unit-fraction packing
in an interval of width at most `c`. -/
def BoundedUnitPacking (k : ℕ) (c : ℝ) : Prop :=
  ∃ n : Fin k → ℕ, UnitPacking k n ∧
    ∃ a b : ℝ, FitsInterval n a b ∧ 0 ≤ b - a ∧ b - a ≤ c

/-- The source's asymptotic notation is formalized as the following faithful
upper-bound reading: for every positive error `ε`, eventually in `k` there is
a unit-fraction packing in an interval of width at most
`(exp 1 - 1 + ε) k`. Here `Real.exp 1` represents the constant `e`.
This records an eventual upper bound rather than separately asserting a matching
lower bound for the widths. -/
def Question : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k : ℕ in atTop,
      ∃ n : Fin k → ℕ, UnitPacking k n ∧
        ∃ a b : ℝ,
          FitsInterval n a b ∧
            0 ≤ b - a ∧ b - a ≤ (Real.exp 1 - 1 + ε) * (k : ℝ)

/-- A proved sanity check: the three distinct positive integers `2`, `3`, and
`6` give the unit-fraction identity
`1/2 + 1/3 + 1/6 = 1`, and they lie in an interval of width `4`. -/
theorem control_three : BoundedUnitPacking 3 4 := by
  refine ⟨![2, 3, 6], ?_, 2, 6, ?_, ?_, ?_⟩
  · unfold UnitPacking
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at hij ⊢
    · norm_num [Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> norm_num
  · norm_num
  · norm_num

/-- Croot's result, as recorded by the source, establishes the formalized
asymptotic upper-bound reading of the question. The mathematical proof is not
reproduced here; this theorem is an explicitly marked literature-dependent gap. -/
theorem croot_result : Question := by
  sorry Erdos286

#print axioms Erdos286.control_three
#print axioms Erdos286.croot_result
