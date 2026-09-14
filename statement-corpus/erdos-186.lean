/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $F(N)$ be the maximal size of $A\subseteq \{1,\ldots,N\}$ which is 'non-averaging', so that no $n\in A$ is the arithmetic mean of at least two elements in $A$. What is the order of growth of $F(N)$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#186 : [Er73,p.118] [Er75b,p.309] [Er77c,p.45] [ErGr79,p.334] [Er80,p.110] [ErGr80,p.18] additive combinatorics Originally due to Straus. It is known that\[N^{1/4}\ll F(N) \ll N^{1/4+o(1)}.\]The lower bound is due to Bosznay [Bo89] and the upper bound to Pham and Zakharov [PhZa24] , improving an earlier bound of Conlon, Fox, and Pham [CFP23] . The original upper bound of Erdős and Sárközy [ErSa90] was $\ll (N\log N)^{1/2}$. See also [789] . This is discussed in problem C16 of Guy's collection [Gu04] . Additional thanks to : Zachary Chase Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 08 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #186, https://www.erdosproblems.com/186, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) OEIS A389784 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Filter

-- @category research solved







open Classical Filter

namespace Erdos186

/-- A finite set of natural numbers is non-averaging when no member is the
arithmetic mean of a subset having at least two distinct elements. The finite
subset is represented by a finset, and the mean equation is cleared of
denominators. -/
def NonAveraging (A : Finset ℕ) : Prop :=
  A.all (fun n =>
      (A.powerset).all (fun B =>
        decide (B.card < 2 ∨ n * B.card ≠ ∑ x ∈ B, x))) = true

/-- The extremal function from the source, represented as the maximum cardinality
among the non-averaging subsets of `{1, ..., N}`. This uses a finite `sup`,
rather than `sSup`, so there is no unbounded- or empty-set default-value issue;
the empty collection of candidates has supremum zero in `ℕ`. -/
def F (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter NonAveraging).sup (fun A => A.card)

/-- A proved small-case control: there is no positive integer in `{1, ..., 0}`,
so the extremal value is zero. -/
theorem F_zero : F 0 = 0 := by
  decide

/-- A proved small-case control: the singleton `{1}` is non-averaging, so the
largest non-averaging subset of `{1}` has cardinality one. -/
theorem F_one : F 1 = 1 := by
  decide

/-- The literal formal translation of the lower estimate
`N^(1/4) ≪ F(N)`, using an eventual positive constant multiple bound. -/
def LowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop,
      c * Real.rpow (N : ℝ) ((1 : ℝ) / 4) ≤ (F N : ℝ)

/-- The literal formal translation of the upper estimate
`F(N) ≪ N^(1/4+o(1))`, expressed by the usual epsilon formulation. -/
def UpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        (F N : ℝ) ≤ C * Real.rpow (N : ℝ) (((1 : ℝ) / 4) + ε)

/-- The source records the problem as settled: the lower and upper estimates
are known. The asymptotic-combinatorial proofs of these literature results
remain an explicit formalization gap here. -/
theorem resolution : LowerBound ∧ UpperBound := by
  sorry

#print axioms F_zero
#print axioms F_one

end Erdos186
