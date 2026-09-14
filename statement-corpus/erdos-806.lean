/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subseteq \{1,\ldots,n\}$ with $\lvert A\rvert \leq n^{1/2}$. Must there exist some $B\subset\mathbb{Z}$ with $\lvert B\rvert=o(n^{1/2})$ such that $A\subseteq B+B$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#806 : [ErNe77] additive combinatorics A problem of Erdős and Newman [ErNe77] , who proved that there exist $A$ with $\lvert A\rvert\asymp n^{1/2}$ such that if $A\subseteq B+B$ then\[\lvert B\rvert \gg \frac{\log\log n}{\log n}n^{1/2}.\]Resolved by Alon, Bukh, and Sudakov [ABS09] , who proved that for any $A\subseteq \{1,\ldots,n\}$ with $\lvert A\rvert \leq n^{1/2}$ there exists some $B$ such that $A\subseteq B+B$ and\[\lvert B\rvert \ll \frac{\log\log n}{\log n}n^{1/2}.\]See also [333] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) (2) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #806, https://www.erdosproblems.com/806, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos806

/-- `AdditivelyCovers A B` means that every element of the target set `A`
belongs to the sumset `B+B`; thus the first argument is the target and the
second argument is the covering set. -/
def AdditivelyCovers (A B : Finset ℤ) : Prop :=
  A ⊆ B.image₂ (fun x y : ℤ => x + y) B

/-- POSITIVE WITNESS: the singleton `{1}` is covered by `{0,1}+{0,1}`. -/
theorem additivelyCovers_witness_pos :
    AdditivelyCovers ({1} : Finset ℤ) ({0, 1} : Finset ℤ) := by
  decide

/-- NEGATIVE WITNESS: removing the zero from the positive covering set makes
the near-miss `{1}` fail, since `{1}+{1}` contains only `2`. -/
theorem additivelyCovers_witness_neg :
    ¬ AdditivelyCovers ({1} : Finset ℤ) ({1} : Finset ℤ) := by
  decide

/-- Convert a finite set of integers in the interval `[1,n]` into a finite
set of integers, forgetting the subtype witness. -/
def forgetInterval (n : ℕ)
    (A : Finset {z : ℤ // z ∈ Finset.Icc (1 : ℤ) n}) : Finset ℤ :=
  A.image (fun z => (z : ℤ))

/-- A bounded, decidable finite-instance test for additive covering. The
quantification is over all finite subsets of the finite interval
`{1,...,n}`, and asks whether each such set has some finite additive cover
inside the same interval. -/
def QuestionFinite (n : ℕ) : Prop :=
  ∀ A : Finset {z : ℤ // z ∈ Finset.Icc (1 : ℤ) n},
    ∃ B : Finset {z : ℤ // z ∈ Finset.Icc (1 : ℤ) n},
      AdditivelyCovers (forgetInterval n A) (forgetInterval n B)

/-- POSITIVE WITNESS: for `n = 0` the interval is empty, so its only finite
subset is covered by the empty set. -/
theorem questionFinite_witness_pos : QuestionFinite 0 := by
  decide

/-- NEGATIVE WITNESS: for `n = 1`, the set `{1}` cannot be covered by a
covering set contained in `{1}`, because `1` is not a sum of two elements of
that interval. -/
theorem questionFinite_witness_neg : ¬ QuestionFinite 1 := by
  decide

/-- The resolved asymptotic statement from Alon, Bukh, and Sudakov,
formalized with the source's little-oh conclusion. The family `A n` records
the varying finite sets; the hypotheses say that each `A n` lies in
`{1,...,n}` and has size at most `n^(1/2)`. The conclusion requires a family
of integer sets covering each `A n` by its sumset and whose normalized
cardinality tends to zero.

SOURCE MAPPING: the source says “for any `A` ... there exists some `B` such
that `A ⊆ B+B` and `|B| = o(n^(1/2))`”; here `A n` and `B n` are the
corresponding sets at scale `n`, `AdditivelyCovers (A n) (B n)` expresses
`A n ⊆ B n + B n`, and the `Tendsto` clause expresses the little-oh bound. -/
theorem alon_bukh_sudakov_resolution :
    ∀ A : ℕ → Finset ℤ,
      (∀ n a, a ∈ A n → 1 ≤ a ∧ a ≤ (n : ℤ)) →
      (∀ n, (A n).card ≤ Nat.sqrt n) →
      ∃ B : ℕ → Finset ℤ,
        (∀ n, AdditivelyCovers (A n) (B n)) ∧
        Tendsto
          (fun n => ((B n).card : ℝ) / Real.sqrt (n : ℝ))
          atTop (𝓝 0) := by
  sorry

#print axioms additivelyCovers_witness_pos
#print axioms additivelyCovers_witness_neg
#print axioms questionFinite_witness_pos
#print axioms questionFinite_witness_neg

end Erdos806
