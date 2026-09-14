/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 2$ and $n_k(p)$ denote the least $k$th power nonresidue of $p$. Is it true that\[\sum_{p<x} n_k(p)\sim c_k \frac{x}{\log x}\]for some constant $c_k>0$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#980 : [Er65b] number theory Erdős [Er61e] proved this when $k=2$, with\[c_2=\sum_{k=1}^\infty \frac{p_k}{2^k}.\]The general case was proved by Elliott [El67b] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #980, https://www.erdosproblems.com/980, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A053760 , A098990 , possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos980

/-- A residue modulo `p` is a `k`th power residue when it is represented by
the `k`th power of some residue modulo `p`. The bounded search makes this
predicate decidable on finite instances. -/
def kthPowerResidueB (k p a : ℕ) : Bool :=
  decide (∃ x ∈ Finset.range p, x ^ k % p = a % p)

/-- POSITIVE WITNESS: modulo `3`, the residue `1` is a square residue. -/
theorem kthPowerResidueB_witness_pos :
    kthPowerResidueB 2 3 1 = true := by
  decide

/-- NEGATIVE WITNESS: modulo `3`, the residue `2` is a near-miss square
residue instance and is not represented by any square modulo `3`. -/
theorem kthPowerResidueB_witness_neg :
    kthPowerResidueB 2 3 2 = false := by
  decide

/-- The least positive `k`th power nonresidue of `p`, with value `0` when
there is no such positive residue. This explicit totalization is needed for
primes for which every residue is a `k`th power; the source's notation
implicitly presupposes existence. No `sInf` is used, so there is no empty-set
or unbounded-set supremum/infimum default involved. -/
noncomputable def leastKthPowerNonresidue (k p : ℕ) : ℕ :=
  if h : ∃ a, 1 ≤ a ∧ kthPowerResidueB k p a = false then
    Nat.find h
  else
    0

/-- The finite sum over primes `p < x` of the least `k`th power nonresidue,
viewed as a real number. -/
noncomputable def primeNonresidueSum (k x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.filter Nat.Prime (Finset.range x)),
    (leastKthPowerNonresidue k p : ℝ)

/-- The source question, formalized as the assertion that for every `k ≥ 2`
there is a positive constant `c` such that the ratio of the prime sum to
`c x / log x` tends to `1` along the natural numbers. -/
def Question : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun x : ℕ =>
          primeNonresidueSum k x /
            (c * (x : ℝ) / Real.log (x : ℝ)))
        atTop (𝓝 1)

/-- A bounded, decidable finite-instance version of the question's basic
`k ≥ 2` and nonresidue conditions. It checks every prime `p ≤ n` that is odd
and asks for a positive nonresidue among the integers at most `n`. -/
def QuestionFinite (k n : ℕ) : Bool :=
  decide
    (2 ≤ k ∧
      ∀ p ∈ Finset.range (n + 1),
        Nat.Prime p →
          p % 2 = 1 →
            ∃ a ∈ Finset.range (n + 1),
              1 ≤ a ∧ kthPowerResidueB k p a = false)

/-- POSITIVE WITNESS: the finite instance with `k = 2` and bound `3`
contains the odd prime `3` and its square nonresidue `2`. -/
theorem QuestionFinite_witness_pos :
    QuestionFinite 2 3 = true := by
  decide

/-- NEGATIVE WITNESS: the near-miss instance changes only the required
inequality `2 ≤ k`, taking `k = 1` while retaining the same finite bound. -/
theorem QuestionFinite_witness_neg :
    QuestionFinite 1 3 = false := by
  decide

/-- The literature resolution recorded in the source: Erdős proved the
case `k = 2`, and Elliott proved the general case. The analytic number
theory proof connecting that result to this formal statement remains an
explicit honest gap. -/
theorem general_case : Question := by
  sorry

#print axioms general_case

end Erdos980
