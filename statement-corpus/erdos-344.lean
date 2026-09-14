/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $A\subseteq \mathbb{N}$ is a set of integers such that\[\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1/2}\]for all $N$ then must $A$ be subcomplete? That is, must\[P(A) = \left\{\sum_{n\in B}n : B\subseteq A\textrm{ finite }\right\}\]contain an infinite arithmetic progression?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#344 : [ErGr80,p.54] number theory | complete sequences Folkman proved this under the stronger assumption that\[\lvert A\cap \{1,\ldots,N\}\rvert\gg N^{1/2+\epsilon}\]for some $\epsilon>0$. This is true, and was proved by Szemerédi and Vu [SzVu06] . The stronger conjecture that this is true under\[\lvert A\cap \{1,\ldots,N\}\rvert\geq (2N)^{1/2}\]seems to be still open (this would be best possible as shown by [Er61b] ). Additional thanks to : Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 28 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #344, https://www.erdosproblems.com/344, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos344

/-- The set of all finite subset sums of a set `A` of natural numbers. -/
def partialSums (A : Set ℕ) : Set ℕ :=
  {m | ∃ s : Finset ℕ, (∀ n ∈ s, n ∈ A) ∧ s.sum id = m}

/-- `A` is subcomplete when its finite subset sums contain an infinite arithmetic progression
with positive common difference. -/
def Subcomplete (A : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ partialSums A

/-- A concrete formalization of the source's notation
`|A ∩ {1,...,N}| ≫ N^(1/2)`: after some threshold, the counting function
is bounded below by a fixed positive multiple of `sqrt N`. -/
def SqrtDense (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    c * Real.sqrt (N : ℝ) ≤
      (((Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ n ∈ A)).card : ℝ)

/-- The source's stronger endpoint conjecture, retained as an open proposition rather than
asserted as a theorem. It uses the exact lower bound `sqrt (2N)` for every positive `N`. -/
def SharpThresholdConjecture : Prop :=
  ∀ A : Set ℕ,
    (∀ N : ℕ, 0 < N →
      Real.sqrt (2 * (N : ℝ)) ≤
        (((Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ n ∈ A)).card : ℝ)) →
    Subcomplete A

/-- The empty finite subset witnesses that zero belongs to the finite subset sums of every set. -/
theorem zero_mem_partialSums (A : Set ℕ) : 0 ∈ partialSums A := by
  refine ⟨∅, ?_, ?_⟩
  · intro n hn
    simp at hn
  · simp

/-- The natural numbers are subcomplete: the singleton finite subset `{k}` represents the
`k`-th term of the arithmetic progression with initial term zero and difference one. -/
theorem subcomplete_univ : Subcomplete (Set.univ : Set ℕ) := by
  refine ⟨0, 1, by decide, ?_⟩
  intro k
  refine ⟨{k}, ?_, ?_⟩
  · intro n hn
    simp
  · simp

/-- The original Erdős problem, formalized with `SqrtDense` and `Subcomplete`.
The resolution node records this statement as true, with the proof attributed to
Szemerédi and Vu [SzVu06]; that external mathematical result remains an explicit
honest proof gap here. -/
theorem sqrtDense_subcomplete (A : Set ℕ) : SqrtDense A → Subcomplete A := by
  sorry

#print axioms zero_mem_partialSums
#print axioms subcomplete_univ

end Erdos344
