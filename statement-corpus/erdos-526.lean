/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $a_n\geq 0$ with $a_n\to 0$ and $\sum a_n=\infty$. Find a necessary and sufficient condition on the $a_n$ such that, if we choose (independently and uniformly) random arcs on the unit circle of length $a_n$, then all the circle is covered with probability $1$.

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#526 : [Er61,p.253] probability | geometry A problem of Dvoretzky [Dv56] . It is easy to see that (under the given conditions alone) almost all the circle is covered with probability $1$. Kahane [Ka59] showed that $a_n=\frac{1+c}{n}$ with $c>0$ has this property, which Erdős (unpublished) improved to $a_n=\frac{1}{n}$. Erdős also showed that $a_n=\frac{1-c}{n}$ with $c>0$ does not have this property. Solved by Shepp [Sh72] , who showed that a necessary and sufficient condition is that\[\sum_n \frac{e^{a_1+\cdots+a_n}}{n^2}=\infty.\] Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #526, https://www.erdosproblems.com/526, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter
open scoped BigOperators

-- @category research solved







open Classical Filter

namespace Erdos526

/-- The hypotheses on the sequence of arc lengths from the question. -/
def Admissible (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧ Tendsto a atTop (𝓝 0) ∧ ¬ Summable a

/-- `ArcContains s l t` means that the arc of length `l` beginning at `s`
contains the point `t` on the unit circle, represented by real parameters
modulo integer translation. -/
def ArcContains (s l t : ℝ) : Prop :=
  ∃ k : ℤ, s ≤ t + (k : ℝ) ∧ t + (k : ℝ) ≤ s + l

/-- `CircleCoveredByStarts a x` is the geometric covering predicate for a
sequence of starting points `x`: every point of the circle belongs to at
least one of the arcs of lengths `a n`. -/
def CircleCoveredByStarts (a x : ℕ → ℝ) : Prop :=
  ∀ t : ℝ, ∃ n, ArcContains (x n) (a n) t

/-- This is the probability-one event in the source: the starts are to be
chosen independently and uniformly on the unit circle, and the resulting
arcs cover the whole circle almost surely.

The underlying infinite product probability-space construction is not yet
formalized here; this declaration is therefore an explicitly named
probabilistic interface rather than a hidden mathematical axiom. -/
noncomputable def AlmostSurelyCircleCovered (a : ℕ → ℝ) : Prop :=
  sorry

/-- The `n`th term in Shepp's criterion, with the finite prefix sum beginning
at index zero and ending at index `n`. -/
def SheppTerm (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (∑ k ∈ Finset.range (n + 1), a k) / ((n + 1 : ℝ) ^ 2)

/-- Divergence of the series appearing in the resolution of the problem. -/
def SheppDiverges (a : ℕ → ℝ) : Prop :=
  ¬ Summable (SheppTerm a)

/-- The geometric arc predicate contains its own left endpoint whenever its
length is nonnegative. -/
theorem arcContains_left_endpoint (s l : ℝ) (hl : 0 ≤ l) :
    ArcContains s l s := by
  refine ⟨0, le_rfl, ?_⟩
  simpa using hl

/-- Every term in Shepp's series is nonnegative. -/
theorem sheppTerm_nonneg (a : ℕ → ℝ) (n : ℕ) :
    0 ≤ SheppTerm a n := by
  unfold SheppTerm
  positivity

/-- The formalized statement of Shepp's resolution.

SOURCE MAPPING: the source asks for a necessary and sufficient condition
under `a_n ≥ 0`, `a_n → 0`, and `∑ a_n = ∞`; the resolution says that the
condition is divergence of
`∑ₙ exp(a₁ + ⋯ + aₙ) / n²`.  `SheppTerm` is the corresponding zero-based
version of that series.

The proof of the probabilistic theorem, as well as the infinite product
probability-space interface represented by `AlmostSurelyCircleCovered`,
remains to be formalized. -/
theorem shepp_criterion (a : ℕ → ℝ) (ha : Admissible a) :
    AlmostSurelyCircleCovered a ↔ SheppDiverges a := by
  sorry

#print axioms arcContains_left_endpoint
#print axioms sheppTerm_nonneg

end Erdos526
