/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A=\{a_1<a_2<\cdots\}\subseteq \mathbb{N}$ be infinite and let $A(x)$ count the number of indices for which $\mathrm{lcm}(a_i,a_{i+1})\leq x$. Is it true that $A(x) \ll x^{1/2}$? How large can\[\liminf \frac{A(x)}{x^{1/2}}\]be?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#440 : [ErGr80,p.87] number theory Taking $A=\mathbb{N}$ shows that\[\liminf \frac{A(x)}{x^{1/2}}=1\]is possible. Erdős and Szemerédi [ErSz80] proved that it is always $\leq 1$. Tao in the comments has given a simple proof that $A(x) \ll x^{1/2}$. van Doorn has proved that $A(x) \leq (c+o(1))x^{1/2}$ where\[c=\sum_{n\geq 1}\frac{1}{n^{1/2}(n+1)}\approx 1.86.\]This was already proved by Erdős and Szemerédi [ErSz80] , who showed that this constant is the best possible. There are more related results (particularly for the more general case of $\mathrm{lcm}(a_i,a_{i+1},\ldots,a_{i+k})$) in [ErSz80] . Additional thanks to : Zachary Chase, Terence Tao, and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (8) Proof claims (0) More information and links This page was last edited 27 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #440, https://www.erdosproblems.com/440, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos440

/-- A valid encoding of an infinite increasing subset of `ℕ`: all terms are
positive and the sequence is strictly increasing. -/
def ValidSequence (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ StrictMono a

/-- The finite counting function used here.  For a positive strictly increasing
sequence, every index contributing at `x` is below `x`, so filtering
`Finset.range x` counts all relevant indices. -/
def indexCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  ((Finset.range x).filter
    (fun i => Nat.lcm (a i) (a (i + 1)) ≤ x)).card

/-- The quotient appearing in the source's liminf question. -/
noncomputable def countRatio (a : ℕ → ℕ) (x : ℕ) : ℝ :=
  (indexCount a x : ℝ) / Real.sqrt (x : ℝ)

/-- Formalization of the assertion that every valid sequence has a square-root
upper bound.  The Vinogradov constant is allowed to depend on the sequence,
which is the direct reading of `A(x) ≪ x^{1/2}` adopted here. -/
def HasSqrtBound : Prop :=
  ∀ a, ValidSequence a →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℕ, 1 ≤ x →
        (indexCount a x : ℝ) ≤ C * Real.sqrt (x : ℝ)

/-- The question recorded by the source, expressed as the square-root bound
for the counting function defined above. -/
def SqrtBoundQuestion : Prop :=
  HasSqrtBound

/-- A precise formulation of having liminf equal to one: the ratio is
eventually within every positive error tolerance of one. -/
def RatioTendsToOne (a : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in atTop,
      1 - ε < countRatio a x ∧ countRatio a x < 1 + ε

/-- The increasing sequence `1, 2, 3, ...`, corresponding to `A = ℕ`. -/
def naturalsSequence : ℕ → ℕ :=
  fun n => n + 1

/-- The canonical sequence is a valid encoding of the set of positive natural
numbers. -/
theorem naturalsSequence_valid : ValidSequence naturalsSequence := by
  constructor
  · intro n
    dsimp [naturalsSequence]
    omega
  · intro i j hij
    dsimp [naturalsSequence]
    omega

/-- Sanity check on the definitions: at `x = 1`, the pair `(1,2)` has lcm
equal to `2`, so the counting function is zero. -/
theorem indexCount_naturals_one : indexCount naturalsSequence 1 = 0 := by
  decide

/-- Resolution of the square-root question in the formalization above.  The
source records Tao's proof that the counting function is `O(x^{1/2})`; the
analytic number-theoretic proof is not reproduced here. -/
theorem tao_sqrt_bound : HasSqrtBound := by
  sorry

/-- Resolution of the extremal example in the source: for `A = ℕ`, the
normalized counting function has liminf equal to one.  This is stated using
the explicit eventual formulation `RatioTendsToOne`; its proof is omitted. -/
theorem naturals_ratio_one : RatioTendsToOne naturalsSequence := by
  sorry

#print axioms naturalsSequence_valid
#print axioms indexCount_naturals_one

end Erdos440
