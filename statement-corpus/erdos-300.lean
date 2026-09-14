/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A(N)$ denote the maximal cardinality of $A\subseteq \{1,\ldots,N\}$ such that $\sum_{n\in S}\frac{1}{n}\neq 1$ for all $S\subseteq A$. Estimate $A(N)$.
-/

/-
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#300 : [ErGr80] [Va99,1.14] number theory | unit fractions Erdős and Graham believe the answer is $A(N)=(1+o(1))N$. Croot [Cr03] disproved this, showing the existence of some constant $c<1$ such that $A(N)<cN$ for all large $N$. It is trivial that $A(N)\geq (1-\frac{1}{e}+o(1))N$. Liu and Sawhney [LiSa24] have proved that $A(N)=(1-1/e+o(1))N$. Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #300, https://www.erdosproblems.com/300, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A390393 Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos300

/-- The reciprocal sum of a finite set of positive integers, viewed in `ℚ`. -/
def unitFractionSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, (n : ℚ)⁻¹

/-- 
A finite set is admissible when it is contained in `{1, ..., N}` and no
subset has reciprocal sum equal to `1`.
-/
def Admissible (N A : ℕ) (s : Finset ℕ) : Prop :=
  s ⊆ Finset.Icc 1 N ∧
    ∀ T ∈ s.powerset, unitFractionSum T ≠ 1

/-- 
The extremal quantity from the source.  The powerset of `Icc 1 N` enumerates
all possible subsets, and the finite supremum takes the largest cardinality
among the admissible ones.  No `sSup` is used, so there is no empty- or
unbounded-set default involved.
-/
noncomputable def AVal (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).powerset.sup
    (fun s => if Admissible N N s then s.card else 0)

/-- The empty set is admissible at every parameter. -/
theorem admissible_empty (N : ℕ) :
    Admissible N N (∅ : Finset ℕ) := by
  simp [Admissible, unitFractionSum]

/-- The reciprocal sum of the empty set is zero. -/
theorem unitFractionSum_empty :
    unitFractionSum (∅ : Finset ℕ) = 0 := by
  simp [unitFractionSum]

/-- A computed control pinning the extremal quantity at the degenerate endpoint `N = 0`. -/
theorem AVal_zero :
    AVal 0 = 0 := by
  simp [AVal, Admissible, unitFractionSum]

/--
The asymptotic answer in normalized form.  The source's phrase
`A(N)=(1-1/e+o(1))N` is read as convergence of `AVal N / N` to
`1 - 1 / exp 1` as `N` tends to infinity.  The theorem below records the
settled Liu--Sawhney result; its proof is not reproduced here.
-/
theorem liu_sawhney_asymptotic :
    Tendsto
      (fun N : ℕ => (AVal N : ℝ) / (N : ℝ))
      atTop
      (𝓝 (1 - 1 / Real.exp 1)) := by
  sorry

#print axioms admissible_empty
#print axioms unitFractionSum_empty
#print axioms AVal_zero

end Erdos300
