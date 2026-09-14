/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f_m(n)$ count the number of maximal sum-free subsets $A\subseteq\{1,\ldots,n\}$ - that is, there are no solutions to $a=b+c$ in $A$ and $A$ is maximal with this property. Estimate $f(n)$ - is it true that $f_m(n)=o(2^{n/2})$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#877 : [CaEr90] [Er98] additive combinatorics A problem of Cameron and Erdős, who proved that $f_m(n)>2^{n/4}$, and also asked whether\[f_m(n)=o(f(n)),\]where $f(n)$ counts the number of all (not necessarily maximal) sum-free sets. Luczak and Schoen [LuSc01] proved that there exists a constant $c<1/2$ such that\[f_m(n)<2^{cn},\]resolving these questions. Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved that\[f_m(n)=2^{(\frac{1}{4}+o(1))n},\]which the same authors [BLST18] later improved to\[f_m(n)=(C_n+o(1))2^{n/4},\]where $C_n$ is some explicit constant depending only on $n\pmod{4}$. See [748] for the non-maximal case. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 02 December 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #877, https://www.erdosproblems.com/877, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A121269 , possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos877

/-- Boolean predicate for a maximal sum-free subset of `{1, ..., n}`.
A set is sum-free when it contains no `a = b + c`, and maximality means
that adjoining any missing element of `{1, ..., n}` destroys sum-freeness. -/
def maximalSumFree (n : ℕ) (A : Finset ℕ) : Bool :=
  decide (
    A ⊆ Finset.Icc 1 n ∧
      (¬ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a = b + c) ∧
      (∀ x ∈ Finset.Icc 1 n, x ∉ A →
        ∃ a ∈ insert x A, ∃ b ∈ insert x A, ∃ c ∈ insert x A, a = b + c))

/-- POSITIVE WITNESS: `{2, 3}` is a maximal sum-free subset of `{1, 2, 3}`. -/
theorem maximalSumFree_witness_pos :
    maximalSumFree 3 ({2, 3} : Finset ℕ) = true := by
  decide

/-- NEGATIVE WITNESS: `{2}` is a near-miss obtained by removing `3` from
the positive witness; it is sum-free but not maximal. -/
theorem maximalSumFree_witness_neg :
    maximalSumFree 3 ({2} : Finset ℕ) = false := by
  decide

/-- The number of maximal sum-free subsets of `{1, ..., n}`. -/
def maximalSumFreeCount (n : ℕ) : ℕ :=
  (Finset.powerset (Finset.Icc 1 n)).filter
    (fun A => maximalSumFree n A = true) |>.card

/-- A finite decidable approximation to the asymptotic estimate, restricted
to the first `N` positive values of `n`. -/
def questionFinite (N : ℕ) : Bool :=
  decide (∀ n ∈ Finset.Icc 1 N,
    maximalSumFreeCount n < 2 ^ (n / 2))

/-- POSITIVE WITNESS: the empty finite range satisfies the bounded test
vacuously. -/
theorem questionFinite_witness_pos :
    questionFinite 0 = true := by
  decide

/-- NEGATIVE WITNESS: the first nonempty range is a near miss; at `n = 1`,
the unique maximal sum-free set gives `f_m(1) = 1`, not strictly less than
`2^(1/2)` interpreted by the source's integer finite approximation as
`2^(1 / 2) = 1`. -/
theorem questionFinite_witness_neg :
    questionFinite 1 = false := by
  decide

/-- The asymptotic question from the source, expressed as convergence of the
ratio to zero. -/
def question : Prop :=
  Tendsto
    (fun n : ℕ =>
      (maximalSumFreeCount n : ℝ) /
        Real.rpow 2 ((n : ℝ) / 2))
    atTop (𝓝 0)

/-- The source's resolution answers the question affirmatively: the maximal
sum-free-set count is little-oh of `2^(n/2)`. This theorem records the
literature result cited in the frozen resolution; its proof remains to be
formalized. -/
theorem question_resolved : question := by
  sorry

#print axioms maximalSumFree_witness_pos
#print axioms maximalSumFree_witness_neg
#print axioms questionFinite_witness_pos
#print axioms questionFinite_witness_neg

end Erdos877
