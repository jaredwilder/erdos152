/-
SOURCE (frozen), node `n000-question`, VERBATIM:
If $A\subseteq \mathbb{N}$ is a multiset of integers such that\[\lvert A\cap \{1,\ldots,N\}\rvert\gg N\]for all $N$ then must $A$ be subcomplete? That is, must\[P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}\]contain an infinite arithmetic progression?
-/

 /-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#343 : [ErGr80,p.54] number theory | complete sequences A problem of Folkman. Folkman [Fo66] showed that this is true if\[\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1+\epsilon}\]for some $\epsilon>0$ and all $N$. The original question was answered by Szemerédi and Vu [SzVu06] (who proved that the answer is yes). This is best possible, since Folkman [Fo66] showed that for all $\epsilon>0$ there exists a multiset $A$ with\[\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1-\epsilon}\]for all $N$, such that $A$ is not subcomplete. Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 02 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #343, https://www.erdosproblems.com/343, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/







import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos343

/-- A multiplicity function on the integers, representing a possibly infinite multiset
of integers. -/
def Multiplicity := ℤ → ℕ

/-- The number of occurrences of integers from `1` through `N` in a multiplicity
function. -/
def intervalCount (A : Multiplicity) (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc (1 : ℤ) (N : ℤ), A n

/-- The linear lower-density condition corresponding to the source notation
`|A ∩ {1,...,N}| ≫ N` for every positive `N`. -/
def HasLinearDensity (A : Multiplicity) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ N : ℕ, 0 < N →
      c * (N : ℝ) ≤ (intervalCount A N : ℝ)

/-- The sum of a finitely supported multiset of integers, with multiplicities. -/
def weightedSum (B : ℤ →₀ ℕ) : ℤ :=
  ∑ n ∈ B.support, (B n : ℤ) * n

/-- The finite subset-sum set `P(A)` from the source, using finitely supported
multiplicity functions `B` satisfying `B ≤ A` pointwise. -/
def subsetSums (A : Multiplicity) : Set ℤ :=
  {x | ∃ B : ℤ →₀ ℕ, (∀ n : ℤ, B n ≤ A n) ∧ x = weightedSum B}

/-- An infinite arithmetic progression contained in a set of integers. -/
def ContainsInfiniteArithmeticProgression (S : Set ℤ) : Prop :=
  ∃ a d : ℤ, 0 < d ∧ ∀ k : ℕ, a + (k : ℤ) * d ∈ S

/-- The source's notion of subcompleteness: the finite subset sums contain an
infinite arithmetic progression. -/
def IsSubcomplete (A : Multiplicity) : Prop :=
  ContainsInfiniteArithmeticProgression (subsetSums A)

/-- The zero finite multiset always contributes the empty sum to `P(A)`. -/
theorem zero_mem_subsetSums (A : Multiplicity) : (0 : ℤ) ∈ subsetSums A := by
  refine ⟨0, ?_, ?_⟩
  · intro n
    simp
  · simp [weightedSum]

/-- Formalization of the settled answer to Erdős Problem 343. The source clause
says that linear lower density forces subcompleteness. Here a multiset is modeled
by an integer-valued multiplicity function, and `subsetSums` uses finite
multiplicity subfunctions. The mathematical implication is attributed in the
resolution to Szemerédi and Vu [SzVu06]; its proof is not reproduced here. -/
theorem linear_density_implies_subcomplete
    (A : Multiplicity) (hA : HasLinearDensity A) :
    IsSubcomplete A := by
  sorry
