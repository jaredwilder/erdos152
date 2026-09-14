/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $N\geq 1$. How many $A\subseteq \{1,\ldots,N\}$ are there such that $\sum_{n\in A}\frac{1}{n}=1$?

NODE n001-resolution (resolution), VERBATIM:
#297 : [ErGr80,p.36] number theory | unit fractions It was not even known for a long time whether this is $2^{cN}$ for some $c<1$ or $2^{(1+o(1))N}$. In fact the former is true, and the correct value of $c$ is now known. Steinerberger [St24] proved the relevant count is at most $2^{0.93N}$; Independently, Liu and Sawhney [LiSa24] gave both upper and lower bounds, proving that the count is\[2^{(0.91\cdots+o(1))N},\]where $0.91\cdots$ is an explicit number defined as the solution to a certain integral equation; Again independently this same asymptotic was proved (with a different proof) by Conlon, Fox, He, Mubayi, Pham, Suk, and Verstraëte [CFHMPSV24] , who prove more generally, for any $x\in \mathbb{Q}_{>0}$, a similar expression for the number of $A\subseteq \{1,\ldots,N\}$ such that $\sum_{n\in A}\frac{1}{n}=x$; The above papers all appeared within weeks of each other in 2024; in 2017 a similar question (with $\leq 1$ rather than $=1$) was asked on MathOverflow by Mikhail Tikhomirov and proofs of the correct asymptotic were sketched by Lucia, RaphaelB4, and js21. See also [362] . Additional thanks to : Zachary Chase Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #297, https://www.erdosproblems.com/297, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A092670 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical
open BigOperators








open Classical Filter

namespace Erdos297

/-- The subsets of `{1, ..., N}` whose reciprocal sum is exactly `1`.
The summation is performed in `ℚ`, so the defining equality is exact rather
than an approximation. -/
def UnitFractionSolutions (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter
    (fun A => ∑ n ∈ A, (1 : ℚ) / (n : ℚ) = 1)

/-- The finite count asked for in Erdős Problem 297. -/
def UnitFractionCount (N : ℕ) : ℕ :=
  (UnitFractionSolutions N).card

/-- A proved small-case control: for `N = 1`, the unique solution is
`A = {1}`. This confirms that the filter is neither identically empty nor
identically full on the stated positive range. -/
theorem unitFractionCount_one : UnitFractionCount 1 = 1 := by
  decide

#print axioms unitFractionCount_one

end Erdos297
