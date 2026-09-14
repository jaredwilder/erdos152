/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Fix some constant $C>0$ and let $N$ be large. Let $A\subseteq \{2,\ldots,N\}$ be such that $(a,b)=1$ for all $a\neq b\in A$ and $\sum_{n\in A}\frac{1}{n}\leq C$. What choice of such an $A$ minimises the number of integers $m\leq N$ not divisible by any $a\in A$?
    
NODE n001-resolution (resolution), VERBATIM:
#783 : [Er73,p.135] number theory Erdős [Er73] suggests that, if $p_i$ is the $i$th prime, then choosing $A=\{p_r<\cdots<p_t\}$, where $p_t$ is the largest prime $\leq N$ and $r$ is minimal such that $\sum_{p\in A}\frac{1}{p}\leq C$ 'either gives the extremal sequence (or at least nearly gives the minimum)'. Chojecki has proved this is the extremal sequence when $C\leq \log 2$. Hunter in the comments notes that there are cases where this is not the literal extremal sequence, since small improving perturbations are possible. Tao suggests the problem (which is likely what Erdős meant) of whether the minimum number of integers in $[1,N]$ not divisible by any $a\in A$ is\[(\rho(e^C)+o(1))N,\]which the construction above shows is achievable. Hildebrand [Hi87b] has proved that this weak form of the conjecture is true if $A$ is a set of primes (answering a question of Erdős and Ruzsa [ErRu80] ). Tao has resolved this question (asymptotically at least), showing that the number of integers not divisible by any $a\in A$ is at least\[(\rho(e^C)+o(1))N,\]where the $o(1)$ term $\to 0$ as $N\to \infty$ with fixed $C$. See also [784] and [1200] . Additional thanks to : Przemek Chojeckl, Wouter van Doorn, Zach Hunter, and Terence Tao Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (28) Proof claims (0) More information and links This page was last edited 28 May 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #783, https://www.erdosproblems.com/783, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable TerenceTao , Przemek Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research open








open Classical Filter

namespace Erdos783

/-- A finite set `A` is admissible when it lies in `{2, ..., N}`, its distinct
members are pairwise coprime, and its reciprocal sum is at most `C`. -/
def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 2 ≤ a ∧ a ≤ N) ∧
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) ∧
    (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) ≤ C

/-- The number of positive integers at most `N` which are divisible by none of
the members of `A`. -/
def Uncovered (N : ℕ) (A : Finset ℕ) : ℕ :=
  (Finset.range N).filter
    (fun k => ∀ a ∈ A, ¬ a ∣ (k + 1))
    |>.card

/-- `A` minimizes the uncovered count among all admissible families for the
fixed parameters `C` and `N`. -/
def IsOptimal (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  Admissible C N A ∧
    ∀ B : Finset ℕ, Admissible C N B → Uncovered N A ≤ Uncovered N B

/-- The exact finite optimization question encoded by Problem #783.  The
source asks which admissible family is optimal; this declaration records that
question as the predicate of having an optimal admissible family, without
asserting a characterization of the optimizer. -/
def Question (C : ℝ) (N : ℕ) : Prop :=
  ∃ A : Finset ℕ, IsOptimal C N A

/-- The empty family is admissible whenever the reciprocal-sum budget is
nonnegative.  This is a proved sanity control showing that the admissibility
predicate has the intended vacuous behavior on the empty family. -/
theorem empty_admissible {C : ℝ} {N : ℕ} (hC : 0 ≤ C) :
    Admissible C N ∅ := by
  simp [Admissible, hC]

/-- With no divisors selected, every positive integer at most `N` is uncovered.
This computes the basic control value of the counting predicate. -/
theorem uncovered_empty (N : ℕ) :
    Uncovered N ∅ = N := by
  simp [Uncovered]

/-- The optimization predicate is monotone in the evident comparison sense:
any optimal family has an uncovered count no larger than that of every other
admissible family. -/
theorem optimal_le {C : ℝ} {N : ℕ} {A : Finset ℕ}
    (hA : IsOptimal C N A) {B : Finset ℕ} (hB : Admissible C N B) :
    Uncovered N A ≤ Uncovered N B :=
  hA.2 B hB

end Erdos783
