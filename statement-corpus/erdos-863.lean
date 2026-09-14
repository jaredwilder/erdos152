/- 
SOURCE (frozen), NODE n000-question (question), VERBATIM:
Let $r\geq 2$ and let $A\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a+b$ with $a\leq b$ for any $n$. (That is, $A$ is a $B_2[r]$ set.) Similarly, let $B\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a-b$ for any $n\geq 1$. If $\lvert A\rvert\sim c_rN^{1/2}$ as $N\to \infty$ and $\lvert B\rvert \sim c_r'N^{1/2}$ as $N\to \infty$ then is it true that $c_r\neq c_r'$ for $r\geq 2$? Is it true that $c_r'<c_r$?

SOURCE (frozen), NODE n001-resolution (resolution), VERBATIM:
#863 : [Er92c,p.39] number theory | sidon sets | additive combinatorics According to Erdős, first formulated in conversation with Berend, and later independently reformulated with Freud. It is true that $c_1=c_1'$, and the classical bound on the size of Sidon sets (see [30] ) implies $c_1=c_1'=1$. Ho and GPT-5.4 Pro have noted that a positive solution follows from arguments in the literature. Indeed, a routine adaptation of the Erdős-Tuán bound for Sidon sets proves that\[\lvert B\rvert\leq (\sqrt{r}+o(1))N^{1/2},\]while Cilleruelo, Ruzsa, and Trujilo [CRT02] have constructed $A$ with\[\lvert A\rvert \geq \left(\frac{r+\lfloor r/2\rfloor}{\sqrt{r+2\lfloor r/2\rfloor}}\right) N^{1/2}.\]Therefore, provided $r\geq 2$,\[c_r'\leq \sqrt{r}<\frac{r+\lfloor r/2\rfloor}{\sqrt{r+2\lfloor r/2\rfloor}}\leq c_r.\](For example, when $r=2$ these give $c_r'\leq \sqrt{2}\approx 1.41$ and $c_r\geq 3/2=1.5$.) Additional thanks to : Ho Boon Suan Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 24 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #863, https://www.erdosproblems.com/863, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos863

/-- The finite additive representation count for pairs `a ≤ b` with `a + b = n`. -/
def additiveRepresentations (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n)

/-- A bounded finite version of the property that `A` is a `B₂[r]` set in
`{1, ..., N}`. The bound `n ≤ 2N` contains every possible relevant sum. -/
def AdditiveB2Finite (N r : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ n ≤ 2 * N, (additiveRepresentations A n).card ≤ r

/-- POSITIVE WITNESS: `{1,2,3}` is a finite additive `B₂[2]` set in
`{1, ..., 3}`. -/
theorem AdditiveB2Finite_witness_pos :
    AdditiveB2Finite 3 2 ({1, 2, 3} : Finset ℕ) := by
  decide

/-- NEGATIVE WITNESS: adjoining `4` to the positive witness violates only
the ambient-set condition for `N = 3`; the representation bound remains at
most `2`. -/
theorem AdditiveB2Finite_witness_neg :
    ¬ AdditiveB2Finite 3 2 ({1, 2, 3, 4} : Finset ℕ) := by
  decide

/-- The finite difference representation count for pairs with `a - b = n`. -/
def differenceRepresentations (B : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (B.product B).filter (fun p => p.1 - p.2 = n)

/-- A bounded finite version of the property that `B` has at most `r`
representations of every positive difference in `{1, ..., N}`. -/
def DifferenceB2Finite (N r : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Icc 1 N ∧
    ∀ n, 1 ≤ n → n ≤ N → (differenceRepresentations B n).card ≤ r

/-- POSITIVE WITNESS: `{1,2,3}` has at most two representations of every
positive difference up to `3`. -/
theorem DifferenceB2Finite_witness_pos :
    DifferenceB2Finite 4 2 ({1, 2, 3} : Finset ℕ) := by
  decide

/-- NEGATIVE WITNESS: adding `4` creates three representations of the
difference `1`, while remaining inside `{1, ..., 4}`. -/
theorem DifferenceB2Finite_witness_neg :
    ¬ DifferenceB2Finite 4 2 ({1, 2, 3, 4} : Finset ℕ) := by
  decide

/-- The numerical strict inequality used in the recorded resolution:
for `r ≥ 2`, the upper bound for the difference problem is strictly below
the lower bound supplied for the additive problem. The floor in the source
is represented by natural-number division `r / 2`. -/
theorem sqrt_lt_additive_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    Real.sqrt (r : ℝ) <
      ((r + r / 2 : ℕ) : ℝ) /
        Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ) := by
  sorry

/-- The resolved conclusion for Erdős problem #863. Here `cA` and `cB`
stand for the asymptotic constants attached respectively to the additive
and difference problems. Assuming the two literature bounds recorded in
the source, the strict numerical inequality gives `cB < cA`, and hence
`cA ≠ cB`. The asymptotic existence and the two literature bounds are not
reproved in this finite formalization. -/
theorem erdos_863_resolution (r : ℕ) (cA cB : ℝ) (hr : 2 ≤ r)
    (hB : cB ≤ Real.sqrt (r : ℝ))
    (hA :
      ((r + r / 2 : ℕ) : ℝ) /
          Real.sqrt ((r + 2 * (r / 2) : ℕ) : ℝ) ≤ cA) :
    cB < cA := by
  sorry

#print axioms AdditiveB2Finite_witness_pos
#print axioms AdditiveB2Finite_witness_neg
#print axioms DifferenceB2Finite_witness_pos
#print axioms DifferenceB2Finite_witness_neg

end Erdos863
