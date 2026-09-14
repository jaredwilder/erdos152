/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
What is the size of the largest $A\subseteq \{1,\ldots,n\}$ such that in the set\[\left\{ \sum_{a\in S} a : \emptyset\neq S\subseteq A\right\}\]no two distinct elements divide each other?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#882 : [Er98] number theory | primitive sets A problem of Erdős and Sárkőzy. The greedy algorithm shows that\[\lvert A\rvert\geq (1-o(1))\log_3 n\]is possible, but Erdős and Sárkőzy speculated that $\lvert A\rvert=(1-o(1))\log_2n$ is possible. In [Er98] Erdős reports (but gives no reference) that Sándor has proved that $\lvert A\rvert=(1-o(1))\log_2 n$ is achievable, taking $A=\{ 2^i+m2^m : 0\leq i<m\}$ and $n=2^{m-1}+m2^m$. Erdős, Lev, Rauzy, Sándor, and Sárközy [ELRSS99] proved that\[\lvert A\rvert > \log_2 n -1\]is achievable, taking $A=\{2^m-2^{m-1},2^m-2^{m-2},\ldots,2^m-1\}$. This property also implies that $\sum_{a\in S}a$ are distinct for distinct subsets $S$, whence [1] implies\[\lvert A\rvert \leq \log_2 n+\tfrac{1}{2}\log_2\log n+O(1),\]and likely $\lvert A\rvert\leq \log_2n+O(1)$. See also [13] . Additional thanks to : Stijn Cambie Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (1) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #882, https://www.erdosproblems.com/882, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/


-- @category research open








import Mathlib
open Classical Filter

namespace Erdos882

/-- The finite set of nonempty subset sums of a finite set `A` of natural numbers. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image (fun S => S.sum id)

/-- `NoComparable S` says that no two distinct members of `S` divide one another. -/
def NoComparable (S : Finset ℕ) : Prop :=
  S.Pairwise (fun x y => ¬ x ∣ y)

/-- A finite set `A` is admissible at scale `n` when it lies in
`{1, ..., n}` and its nonempty subset sums are pairwise non-dividing. -/
def Admissible (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧ NoComparable (subsetSums A)

/-- The finite-search version of the largest size in the source question.
The supremum is taken over the finite collection of all subsets of
`{1, ..., n}`; hence it is not subject to the empty or unbounded `sSup`
default-value issue. -/
def largestSize (n : ℕ) : ℕ :=
  (Finset.filter (fun A : Finset ℕ => Admissible n A)
    (Finset.Icc 1 n).powerset).sup (fun A => A.card)

/-- POSITIVE WITNESS: `{2, 3}` is admissible at scale `3`. -/
theorem admissible_witness_pos : Admissible 3 ({2, 3} : Finset ℕ) := by
  decide

/-- NEGATIVE WITNESS: `{2, 3, 4}` is a near miss at scale `4`; it lies in
`{1, ..., 4}`, but the distinct subset sums `2` and `4` are comparable by
divisibility. -/
theorem admissible_witness_neg : ¬ Admissible 4 ({2, 3, 4} : Finset ℕ) := by
  decide

/-- A concrete control computation: at `n = 3`, the largest admissible
finite set has cardinality `2`. -/
theorem largestSize_three : largestSize 3 = 2 := by
  decide

/-- The finite formalization of the source's question: `k` is the largest
admissible cardinality at scale `n`. This records the exact finite
optimization problem, while the asymptotic claims in the resolution remain
research statements and are not asserted here. -/
def IsLargestCard (n k : ℕ) : Prop :=
  k = largestSize n

/-- POSITIVE WITNESS: `2` is the largest admissible cardinality at scale `3`. -/
theorem isLargestCard_witness_pos : IsLargestCard 3 2 := by
  exact largestSize_three

/-- NEGATIVE WITNESS: `3` is a near-miss answer at scale `3`, differing from
the correct answer by exactly one in the proposed cardinality. -/
theorem isLargestCard_witness_neg : ¬ IsLargestCard 3 3 := by
  simp [IsLargestCard, largestSize_three]

/-- The source's finite optimization is attained because the search space is
a finite powerset and contains the empty set. The remaining proof is the
general finite-max argument connecting the computed supremum to an attaining
admissible set. -/
theorem largestSize_attained (n : ℕ) :
    ∃ A : Finset ℕ, Admissible n A ∧ A.card = largestSize n := by
  sorry

#print axioms largestSize_three

end Erdos882
