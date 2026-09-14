/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Estimate the maximum of $F(A,B)$ as $A,B$ range over all subsets of $\{1,\ldots,N\}$, where $F(A,B)$ counts the number of $m$ such that $m=ab$ has exactly one solution (with $a\in A$ and $b\in B$).

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#896 : [Er72,p.81] number theory The order of magnitude of $F(A,B)$ is now known:\[F(A,B)\asymp \frac{N^2}{(\log N)^\delta(\log\log N)^{3/2}}\]where $\delta=1-\frac{1+\log\log 2}{\log 2}\approx 0.086$. The upper bound is an immediate consequence of the bound on the size of $\{1,\ldots,N\}\cdot\{1,\ldots,N\}$ given by Ford [Fo08] . The lower bound was proved by GPT-5.5 Pro (prompted by Chojecki), using a similar result from [Fo08] ; the proof is sketched in the comments. See also [490] . Additional thanks to : Przemek Chohecki and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (5) Proof claims (0) More information and links This page was last edited 02 May 2026 ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #896, https://www.erdosproblems.com/896, accessed 2026-08-30 From the external database . You can help update this.
-/






import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos896

/-- The finite universe of positive integers from `1` through `N`. -/
def universe (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- `Admissible N A` means that `A` is a subset of `{1, ..., N}`. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ universe N

/-- POSITIVE WITNESS: `{1}` is a subset of `{1, ..., 2}`. -/
theorem admissible_witness_pos : Admissible 2 ({1} : Finset ℕ) := by
  decide

/-- NEGATIVE WITNESS: adjoining `0` to the positive witness breaks exactly the subset condition. -/
theorem admissible_witness_neg : ¬ Admissible 2 ({0, 1} : Finset ℕ) := by
  decide

/-- The number of representations of `m` as `a * b` with `a ∈ A` and `b ∈ B`. -/
def representationCount (A B : Finset ℕ) (m : ℕ) : ℕ :=
  (A.product B).filter (fun p => p.1 * p.2 = m) |>.card

/-- `HasUniqueProduct N A B m` says that `m` lies in the relevant range and has
exactly one representation as `a*b` with `a ∈ A` and `b ∈ B`. -/
def HasUniqueProduct (N : ℕ) (A B : Finset ℕ) (m : ℕ) : Prop :=
  m ∈ Finset.Icc 1 (N * N) ∧ representationCount A B m = 1

/-- POSITIVE WITNESS: `1 = 1 * 1` has exactly one representation from the singleton sets. -/
theorem hasUniqueProduct_witness_pos :
    HasUniqueProduct 2 ({1} : Finset ℕ) ({1} : Finset ℕ) 1 := by
  decide

/-- NEGATIVE WITNESS: the nearby value `2` has no representation from the same singleton sets. -/
theorem hasUniqueProduct_witness_neg :
    ¬ HasUniqueProduct 2 ({1} : Finset ℕ) ({1} : Finset ℕ) 2 := by
  decide

/-- `F N A B` counts the integers in the product range having exactly one
representation with a factor in `A` and a factor in `B`. -/
def F (N : ℕ) (A B : Finset ℕ) : ℕ :=
  (Finset.Icc 1 (N * N)).filter
    (fun m => representationCount A B m = 1) |>.card

/-- A concrete computed control showing that the definition of `F` is nontrivial. -/
theorem F_control : F 2 ({1} : Finset ℕ) ({1} : Finset ℕ) = 1 := by
  decide

/-- The maximum is taken over all pairs of subsets of `{1, ..., N}`.
This is a finite `Finset.sup`, not an `sSup`; hence there is no unbounded-set
default-value issue. The nonempty finite universe is also exercised by
`F_control`. -/
def maxF (N : ℕ) : ℕ :=
  (universe N).powerset.sup (fun A =>
    (universe N).powerset.sup (fun B => F N A B))

/-- The finite maximum is attained by some pair of subsets. The remaining
proof is a finite extremal argument over the two powersets. -/
theorem maxF_is_attained (N : ℕ) :
    ∃ A B : Finset ℕ,
      Admissible N A ∧ Admissible N B ∧ F N A B = maxF N := by
  sorry

/-- The maximum dominates every admissible value. The remaining proof is the
corresponding pair of `Finset.sup` inequalities. -/
theorem F_le_maxF (N : ℕ) (A B : Finset ℕ)
    (hA : Admissible N A) (hB : Admissible N B) :
    F N A B ≤ maxF N := by
  sorry

/-- The exponent appearing in the recorded asymptotic estimate. -/
noncomputable def delta : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- The real-valued scale
`N^2 / ((log N)^delta (log log N)^(3/2))`, using real powers. -/
noncomputable def asymptoticScale (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 : ℕ) /
    (Real.rpow (Real.log (N : ℝ)) delta *
      Real.rpow (Real.log (Real.log (N : ℝ))) ((3 : ℝ) / 2))

/-- Formal reading of the source's resolution: there are positive constant
multiplicative bounds, valid from some threshold onward, between the finite
maximum of `F` and the displayed asymptotic scale. The source records this as
known; the analytic number-theoretic proof of these bounds remains an explicit
formalization gap here. -/
theorem erdos896_resolution :
    ∃ c C : ℝ, ∃ N₀ : ℕ,
      0 < c ∧ c ≤ C ∧
      ∀ N : ℕ, N₀ ≤ N →
        c * asymptoticScale N ≤ (maxF N : ℝ) ∧
        (maxF N : ℝ) ≤ C * asymptoticScale N := by
  sorry

#print axioms admissible_witness_pos
#print axioms admissible_witness_neg
#print axioms hasUniqueProduct_witness_pos
#print axioms hasUniqueProduct_witness_neg
#print axioms F_control

end Erdos896
