/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $N(X,\delta)$ denote the maximum number of points $P_1,\ldots,P_n$ which can be chosen in a circle of radius $X$ such that\[\| \lvert P_i-P_j\rvert \| \geq \delta\]for all $1\leq i<j\leq n$. (Here $\|x\|$ is the distance from $x$ to the nearest integer.) Is it true that, for any $0<\delta<1/2$, we have\[N(X,\delta)=o(X)?\]In fact, is it true that (for any fixed $\delta>0$)\[N(X,\delta)<X^{1/2+o(1)}?\]
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#465 : [ErGr80] [Er82e] number theory The first conjecture was proved by Sárközy [Sa76] , who in fact proved\[N(X,\delta) \ll \delta^{-3}\frac{X}{\log\log X}.\]Konyagin [Ko01] proved the strong upper bound\[N(X,\delta) \ll_\delta X^{1/2}.\]See also [466] for lower bounds and [953] for a similar problem. Additional thanks to : Vjekoslav Kovac and Stefan Steinerberger Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 18 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #465, https://www.erdosproblems.com/465, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/







import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos465

/-- Points in the Euclidean plane, using the Euclidean rather than the product metric. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The distance from a real number to the nearer of the two adjacent integers. -/
def integerDistance (x : ℝ) : ℝ :=
  min (|x - (Int.floor x : ℝ)|) (|(Int.ceil x : ℝ) - x|)

/-- A finite set of points in the circle of radius `X` satisfying the required
pairwise separation condition. -/
def Admissible (X δ : ℝ) (A : Finset Point) : Prop :=
  (∀ p ∈ A, p ∈ Metric.closedBall (0 : Point) X) ∧
    (∀ p ∈ A, ∀ q ∈ A, p ≠ q →
      δ ≤ integerDistance (dist p q))

/-- The set of cardinalities of admissible finite configurations. -/
def cardinalSet (X δ : ℝ) : Set ℕ :=
  {n : ℕ | ∃ A : Finset Point, Admissible X δ A ∧ A.card = n}

/-- `N(X,δ)` is defined as the supremum of the attainable cardinalities.
The use of `sSup` is mathematically legitimate only after establishing that this
set is nonempty and bounded above; those two facts are recorded below, rather
than relying on the junk value of `sSup` for an empty or unbounded set. -/
noncomputable def N (X δ : ℝ) : ℕ :=
  sSup (cardinalSet X δ)

/-- The empty configuration is admissible, providing nonemptiness of the
cardinality set independently of any packing estimate. -/
theorem empty_admissible (X δ : ℝ) : Admissible X δ ∅ := by
  constructor
  · simp
  · simp

/-- The attainable cardinality set is nonempty because it contains zero. -/
theorem cardinalSet_nonempty (X δ : ℝ) :
    (cardinalSet X δ).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨∅, empty_admissible X δ, ?_⟩
  simp

/-- The integer-distance function vanishes at zero. -/
theorem integerDistance_zero : integerDistance 0 = 0 := by
  simp [integerDistance]

/-- A singleton at the centre is admissible whenever its required separation
parameter is positive. -/
theorem singleton_admissible {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ) :
    Admissible X δ ({(0 : Point)} : Finset Point) := by
  constructor
  · intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    simp [Metric.mem_closedBall, hX]
  · intro p hp q hq hpq
    simp only [Finset.mem_singleton] at hp hq
    subst p
    subst q
    exact (hpq rfl).elim

/-- The cardinality set is bounded above for positive separation.  This is
the finite Euclidean packing estimate needed to ensure that the `sSup`
defining `N` is not its unbounded-set default. -/
theorem cardinalSet_bddAbove {X δ : ℝ} (hδ : 0 < δ) :
    BddAbove (cardinalSet X δ) := by
  sorry

/-- The source's first question, formalized using convergence at infinity. -/
def FirstConclusion : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    Tendsto (fun X : ℝ => (N X δ : ℝ) / X) atTop (𝓝 0)

/-- The strong square-root upper bound recorded in the resolution. -/
def StrongConclusion : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ, 0 < C ∧
      ∀ X : ℝ, 1 ≤ X → (N X δ : ℝ) ≤ C * Real.sqrt X

/-- Sárközy's resolved answer to the first question.  The proof of the
number-theoretic packing estimate is not reproduced here. -/
theorem sarkozy_resolution : FirstConclusion := by
  sorry

/-- Konyagin's stronger resolved upper bound, formalized in an explicit
constant form.  The dependence of `C` on the fixed positive `δ` is allowed,
as in the source's notation `≪_δ`. -/
theorem konyagin_resolution : StrongConclusion := by
  sorry

#print axioms empty_admissible
#print axioms integerDistance_zero
#print axioms singleton_admissible

end Erdos465
