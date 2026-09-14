/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $r\geq 1$ and define $T(n,r)$ to be maximal such that there exists a family $\mathcal{F}$ of subsets of $\{1,\ldots,n\}$ of size $T(n,r)$ such that $\lvert A\cap B\rvert\neq r$ for all $A,B\in \mathcal{F}$. Estimate $T(n,r)$ for $r\geq 2$. In particular, is it true that for every $\epsilon>0$ there exists $\delta>0$ such that for all $\epsilon n<r<(1/2-\epsilon) n$ we have\[T(n,r)<(2-\delta)^n?\]
-/

/- 
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#703 : [Er75f,p.108] [Er76b] [Er81] [Er82e] combinatorics It is trivial that $T(n,0)=2^{n-1}$. Frankl and Füredi [FrFu84b] proved that, for fixed $r$ and $n$ sufficiently large in terms of $r$, the maximal $T(n,r)$ is achieved by taking\[\mathcal{F} = \left\{ A\subseteq \{1,\ldots,n\} : \lvert A\rvert> \frac{n+r}{2}\textrm{ or }\lvert A\rvert < r\right\}\]when $n+r$ is odd, and\[\mathcal{F} = \left\{ A\subseteq \{1,\ldots,n\} : \lvert A\backslash \{1\}\rvert\geq \frac{n+r}{2}\textrm{ or }\lvert A\rvert < r\right\}\]when $n+r$ is even. (Frankl [Fr77b] had earlier proved this for $r=1$ and all $n$.) An affirmative answer to the second question implies that the chromatic number of the unit distance graph in $\mathbb{R}^n$ (with two points joined by an edge if the distance between them is $1$) grows exponentially in $n$, which was proved by alternative methods by Frankl and Wilson [FrWi81] - see [704] . The answer to the second question is yes, proved by Frankl and Rödl [FrRo87] . See also [702] . Additional thanks to : Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 16 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #703, https://www.erdosproblems.com/703, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) OEIS A390645 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous <a href="/7
-/

import Mathlib
open Classical

-- @category research solved

namespace Erdos703

/-- A family of subsets of `Fin n` avoids intersection size `r` for every pair of distinct members. -/
def AdmissibleFamily (n r : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A B : Finset (Fin n)⦄,
    A ∈ F → B ∈ F → A ≠ B → (A ∩ B).card ≠ r

/-- The finite extremal quantity `T(n,r)`, defined as the largest cardinality of an admissible family.

The distinctness condition on `A` and `B` is the standard pairwise interpretation of the
source's phrase “for all `A,B ∈ 𝓕`”; it also agrees with the source's recorded value at `r = 0`. -/
noncomputable def T (n r : ℕ) : ℕ :=
  let families : Finset (Finset (Finset (Fin n))) :=
    Finset.univ.filter
      (fun F : Finset (Finset (Fin n)) => decide (AdmissibleFamily n r F))
  families.sup Finset.card

/-- The empty family is admissible for every ground set and every forbidden intersection size. -/
theorem empty_admissible (n r : ℕ) :
    AdmissibleFamily n r (∅ : Finset (Finset (Fin n))) := by
  intro A B hA hB hne
  simp at hA

/-- The extremal quantity is always a natural number and hence is nonnegative. -/
theorem t_nonneg (n r : ℕ) : 0 ≤ T n r :=
  Nat.zero_le _

/-- The affirmative asymptotic assertion asked in the source, expressed using real inequalities. -/
def SecondQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n r : ℕ,
        ε * (n : ℝ) < (r : ℝ) →
        (r : ℝ) < (1 / 2 - ε) * (n : ℝ) →
        (T n r : ℝ) < (2 - δ) ^ n

#print axioms empty_admissible
#print axioms t_nonneg

end Erdos703