/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)$ count the number of sum-free $A\subseteq \{1,\ldots,n\}$, i.e. $A$ contains no solutions to $a=b+c$ with $a,b,c\in A$. Is it true that\[f(n)=2^{(1+o(1))\frac{n}{2}}?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#748 : [CaEr90] [Er94b] [Er98] number theory The Cameron-Erdős conjecture . It is trivial to see that $f(n) \geq 2^{\frac{n}{2}}$, considering all subsets of $[n/2,n]$. This is true, and in fact $f(n) \ll 2^{n/2}$, which was proved independently by Green [Gr04] and Sapozhenko [Sa03] . In fact, both papers prove the stronger asymptotic $f(n) \sim c_n 2^{n/2}$, where $c_n$ takes on one of two values depending on the parity of $n$. See [877] for the maximal case. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #748, https://www.erdosproblems.com/748, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A007865 Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos748

/-- The finite set of pairwise sums of elements of a finite set `A`. -/
def pairwiseSums (A : Finset ℕ) : Finset ℕ :=
  A.biUnion (fun a => A.image (fun b => a + b))

/-- A finite set is sum-free when it is disjoint from its pairwise sums. -/
def SumFree (A : Finset ℕ) : Prop :=
  A ∩ pairwiseSums A = ∅

/-- The number `f(n)` of sum-free subsets of `{1, ..., n}`. -/
def f (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter SumFree).card

/-- The normalized logarithmic formulation of
`f(n) = 2^((1+o(1)) n/2)`. -/
def AsymptoticQuestion : Prop :=
  Tendsto
    (fun n : ℕ =>
      Real.log (f n : ℝ) / (((n : ℝ) / 2) * Real.log 2))
    atTop (𝓝 1)

/-- A proved control showing that the sum-free predicate is not vacuous:
the singleton `{1}` is sum-free. -/
theorem sumFree_singleton_one : SumFree ({1} : Finset ℕ) := by
  decide

/-- A proved finite control on the counting definition: the only subsets of
`{1}` are sum-free, so `f(1) = 2`. -/
theorem f_one : f 1 = 2 := by
  decide

#print axioms sumFree_singleton_one
#print axioms f_one

/-- The Cameron–Erdős conjecture in the logarithmic asymptotic formulation.
The source records this statement as settled by Green and Sapozhenko; the
proof of that literature result is not reproduced here, so this declaration
is an explicit honest gap rather than an asserted axiom. -/
theorem cameron_erdos_rate : AsymptoticQuestion := by
  sorry Erdos748
