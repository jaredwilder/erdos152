/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k(N)$ denote the size of the largest set $A\subseteq \{1,\ldots,N\}$ such that the sets\[S_r = \{ a_1+\cdots +a_r : a_1<\cdots<a_r\in A\}\]are disjoint for distinct $r\geq 1$. Estimate $k(N)$ - in particular, is it true that $k(N)\sim 2N^{1/2}$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#874 : [Er62c] [Er98] number theory | additive combinatorics Straus [St66] calls such sets admissible, and proved that\[\limsup \frac{k(N)}{N^{1/2}}\leq \frac{4}{\sqrt{3}}=2.309\cdots,\]and that $A=(N-k,N]\cap \mathbb{N}$ has this property for $k=2m-1$ if $N\in [m^2,m^2+m)$ and for $k=2m$ if $N\in [m^2+m,(m+1)^2)$, which implies that\[\liminf \frac{k(N)}{N^{1/2}}\geq 2.\]Erdős, Nicolas, and Sárközy [ENS91] improved the upper bound to\[\limsup \frac{k(N)}{N^{1/2}}\leq (143/27)^{1/2}=2.301\cdots.\]The conjecture was proved (for all large $N$) by Deshouillers and Freiman [DeFr99] , who further show that in some cases the largest such $A$ has the form $(N-k,N]\cap \mathbb{N}$ as above. See also [186] and [789] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #874, https://www.erdosproblems.com/874, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos874

/-- The set of sums of exactly `r` distinct elements of the finite set `A`. -/
def subsetSums (A : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (A.powerset.filter (fun B => B.card = r)).image (fun B => ∑ a ∈ B, a)

/-- A bounded, decidable version of admissibility: the sumsets for all
positive sizes at most `n` are pairwise disjoint. -/
def admissibleFinite (A : Finset ℕ) (n : ℕ) : Bool :=
  (Finset.Icc 1 n).all (fun r₁ =>
    (Finset.Icc 1 n).all (fun r₂ =>
      decide (r₁ = r₂ ∨ Disjoint (subsetSums A r₁) (subsetSums A r₂))))

/-- POSITIVE WITNESS: the two-element set `{1, 2}` has disjoint sumsets
for the sizes occurring in its cardinality bound. -/
theorem admissibleFinite_witness_pos :
    admissibleFinite ({1, 2} : Finset ℕ) 2 = true := by
  decide

/-- NEGATIVE WITNESS: `{1, 2, 3}` is a near-miss obtained by adding one
element to the positive witness; the singleton sum `3` meets the two-element
sum `1 + 2`. -/
theorem admissibleFinite_witness_neg :
    admissibleFinite ({1, 2, 3} : Finset ℕ) 3 = false := by
  decide

/-- The finite candidate families contained in `{1, ..., N}`. -/
def candidateFamilies (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset

/-- The extremal cardinality obtained by maximizing over admissible finite
subsets of `{1, ..., N}`. The admissibility bound is the cardinality of the
candidate itself, so every nonempty possible sumset size is tested. -/
def k (N : ℕ) : ℕ :=
  ((candidateFamilies N).filter
      (fun A => admissibleFinite A A.card = true)).sup Finset.card

/-- POSITIVE WITNESS: at `N = 2`, the extremal admissible set has size `2`. -/
theorem k_witness_pos : k 2 = 2 := by
  decide

/-- NEGATIVE WITNESS: at `N = 3`, the full three-element candidate is rejected
by the single collision `3 = 1 + 2`, while the two-element candidates remain
admissible. -/
theorem k_witness_neg : k 3 = 2 := by
  decide

/-- The resolved asymptotic statement for Erdős problem #874. The source's
question asks whether `k(N) ∼ 2 N^(1/2)`; the resolution says this conjecture
is true for all sufficiently large `N`. The definition of `k` above is a
finite maximum, so no unbounded `sSup` or `sInf` default value is involved.
The proof is not reproduced here; the remaining gap is the theorem of
Deshouillers and Freiman cited in the source. -/
theorem k_tendsto_two :
    Tendsto (fun N : ℕ => (k N : ℝ) / Real.sqrt (N : ℝ))
      atTop (𝓝 (2 : ℝ)) := by
  sorry

#print axioms admissibleFinite_witness_pos
#print axioms admissibleFinite_witness_neg
#print axioms k_witness_pos
#print axioms k_witness_neg

end Erdos874
