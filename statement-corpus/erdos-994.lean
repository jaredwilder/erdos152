/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $E\subseteq (0,1)$ be a meaurable subset with Lebesgue measure $\lambda(E)$. Is it true that, for almost all $\alpha$,\[\lim_{n\to \infty}\frac{1}{n}\sum_{1\leq k\leq n}1_{\{k\alpha \}\in E}=\lambda(E)\]for all $E$?
    
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#994 : [Er64b] analysis | discrepancy A conjecture of Khintchine [Kh23] . In fact this is false, and was disproved by Marstrand [Ma70] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #994, https://www.erdosproblems.com/994, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos994

/-- The finite orbit average of the indicator of `E` along the sequence `{k α}`,
with the empty average at `n = 0` defined to be zero. -/
noncomputable def orbitAverage (E : Set ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then
    0
  else
    (∑ k ∈ Finset.Icc 1 n,
      if Int.fract ((k : ℝ) * α) ∈ E then 1 else 0) / (n : ℝ)

/-- Formalization of the question in the source.

The phrase “for almost all α” is represented by an almost-everywhere
quantifier for Lebesgue measure on `ℝ`; the universal quantifier over `E`
is restricted to measurable subsets of `(0,1)`, as in the source. -/
def Question : Prop :=
  ∀ᶠ α in volume,
    ∀ E : Set ℝ, E ⊆ Set.Ioo (0 : ℝ) 1 → MeasurableSet E →
      Tendsto (fun n : ℕ => orbitAverage E α n) atTop
        (𝓝 ((volume E).toReal))

/-- A decidable bounded control for the finite empirical version of the
question: among four sample positions, a half-measure set should be hit
twice. This is only a finite sanity check and is not asserted to be
equivalent to the infinite statement `Question`. -/
def FiniteQuestion (hits : Finset (Fin 4)) : Prop :=
  hits.card = 2

/-- POSITIVE WITNESS: two of four sample positions are hits, as required by
the finite half-measure control. -/
theorem finiteQuestion_witness_pos :
    FiniteQuestion ({0, 1} : Finset (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: the near-miss obtained from the positive witness by
removing exactly one hit. -/
theorem finiteQuestion_witness_neg :
    ¬ FiniteQuestion ({0} : Finset (Fin 4)) := by
  decide

/-- The finite control is genuinely directional: the positive and
near-miss instances have different truth values. -/
theorem finiteQuestion_control :
    FiniteQuestion ({0, 1} : Finset (Fin 4)) ∧
      ¬ FiniteQuestion ({0} : Finset (Fin 4)) := by
  exact ⟨finiteQuestion_witness_pos, finiteQuestion_witness_neg⟩

/-- Resolution recorded by the source: the Khintchine assertion formalized
as `Question` is false. The proof of Marstrand's counterexample remains an
honest external gap here. -/
theorem marstrand_resolution : ¬ Question := by
  sorry Erdos994

#print axioms Erdos994.finiteQuestion_witness_pos
#print axioms Erdos994.finiteQuestion_witness_neg
#print axioms Erdos994.finiteQuestion_control
