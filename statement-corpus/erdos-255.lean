/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $z_1,z_2,\ldots \in [0,1]$ be an infinite sequence, and define the discrepancy\[D_N(I) = \#\{ n\leq N : z_n\in I\} - N\lvert I\rvert.\]Must there exist some interval $I\subseteq [0,1]$ such that\[\limsup_{N\to \infty}\lvert D_N(I)\rvert =\infty?\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#255 : [Er61] [Er64b] discrepancy The answer is yes, as proved by Schmidt [Sc68] , who later showed [Sc72] that in fact this is true for all but countably many intervals of the shape $[0,x]$. Essentially the best possible result was proved by Tijdeman and Wagner [TiWa80] , who proved that, for almost all intervals of the shape $[0,x)$, we have\[\limsup_{N\to \infty}\frac{\lvert D_N([0,x))\rvert}{\log N}\gg 1.\] Additional thanks to : Cedric Pilatte and Stefan Steinerberger Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #255, https://www.erdosproblems.com/255, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos255

/-- A closed interval contained in `[0,1]`. -/
structure Interval where
  lo : ℝ
  hi : ℝ
  lo_nonneg : 0 ≤ lo
  hi_le_one : hi ≤ 1
  le_hi : lo ≤ hi

/-- Membership of a real number in an interval. -/
def inInterval (I : Interval) (x : ℝ) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi

/-- The full interval `[0,1]`. -/
def fullInterval : Interval :=
  { lo := 0
    hi := 1
    lo_nonneg := by norm_num
    hi_le_one := by norm_num
    le_hi := by norm_num }

/-- The discrepancy, counting the first `N` terms of a sequence indexed from `0`.
The term `z (n + 1)` represents the source's `z_n`, and `N` terms are counted,
corresponding to the source's convention `n ≤ N`. -/
def discrepancy (z : ℕ → ℝ) (I : Interval) (N : ℕ) : ℝ :=
  ((Finset.filter (fun n => inInterval I (z (n + 1))) (Finset.range N)).card : ℝ) -
    (N : ℝ) * (I.hi - I.lo)

/-- The assertion that the absolute discrepancy is arbitrarily large along
arbitrarily late values of `N`; this is the formal encoding of
`limsup_{N → ∞} |D_N(I)| = ∞`. -/
def InfiniteLimsup (z : ℕ → ℝ) (I : Interval) : Prop :=
  ∀ C : ℝ, ∀ M : ℕ, ∃ N : ℕ,
    M ≤ N ∧ C ≤ |discrepancy z I N|

/-- The formalized question: for every sequence in `[0,1]`, does there exist
an interval in `[0,1]` whose discrepancy has infinite limsup? -/
def Question : Prop :=
  ∀ z : ℕ → ℝ,
    (∀ n, 0 ≤ z n ∧ z n ≤ 1) →
      ∃ I : Interval, InfiniteLimsup z I

/-- Sanity control: for the constant zero sequence and the full interval,
the discrepancy is identically zero. This exercises the counting and length
parts of the definition and shows that the predicate is not definitionally
always true. -/
theorem constant_zero_control (N : ℕ) :
    discrepancy (fun _ => (0 : ℝ)) fullInterval N = 0 := by
  simp [discrepancy, inInterval, fullInterval]

#print axioms constant_zero_control

/-- Schmidt's positive answer to Erdős Problem #255.
The source clause is “Must there exist some interval `I ⊆ [0,1]` such that
`limsup |D_N(I)| = ∞`?”, and the resolution records that the answer is yes.
The proof of the mathematical discrepancy theorem remains an explicit gap here. -/
theorem answer_yes : Question := by
  sorry Erdos255
