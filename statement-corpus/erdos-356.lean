/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there some $c>0$ such that, for all sufficiently large $n$, there exist integers $a_1<\cdots<a_k\leq n$ such that there are at least $cn^2$ distinct integers of the form $\sum_{u\leq i\leq v}a_i$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#356 : [ErGr80,p.58] number theory This fails for $a_i=i$ for example. Erdős and Graham also ask what happens if we drop the monotonicity restriction and just ask that the $a_i$ are distinct. They speculated that perhaps some permutation of $\{1,\ldots,n\}$ has at least $cn^2$ such distinct sums - this is true, as proved by Konieczny [Ko15] (see [34] ). The original problem was solved (in the affirmative) by Beker [Be23b] . They also ask how many consecutive integers $>n$ can be represented as such a sum? Is it true that, for any $c>0$ at least $cn$ such integers are possible (for sufficiently large $n)? See also [34] , [357] , and [358] . Additional thanks to : Adrian Beker Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 16 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #356, https://www.erdosproblems.com/356, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes Woett Open to collaboration Woett Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos356

/-- The sum of the terms of `a` on the integer interval from `u` to `v`.
This uses indices in `Fin k`, so it represents sums of the form
`∑_{u ≤ i ≤ v} a_i` from the source. -/
def intervalSum {k : ℕ} (a : Fin k → ℤ) (u v : Fin k) : ℤ :=
  ∑ i ∈ Finset.Icc u v, a i

/-- The finite set of all consecutive interval sums of the sequence `a`.
The first argument of each pair is required to be at most the second. -/
def represented {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  ((Finset.univ.product Finset.univ).filter
      (fun p : Fin k × Fin k => p.1 ≤ p.2)).image
    (fun p => intervalSum a p.1 p.2)

/-- Admissibility of a finite integer sequence for the parameter `n`: its terms
are strictly increasing and every term is at most `n`. -/
def Admissible (n k : ℕ) (a : Fin k → ℤ) : Prop :=
  StrictMono a ∧ ∀ i, a i ≤ (n : ℤ)

/-- The source's quantitative property at `n` and constant `c`: there is an
admissible increasing integer sequence whose set of consecutive sums has
cardinality at least `c n^2`. -/
def HasManySums (n : ℕ) (c : ℝ) : Prop :=
  ∃ k : ℕ, ∃ a : Fin k → ℤ,
    Admissible n k a ∧
      ((represented a).card : ℝ) ≥ c * (n : ℝ) ^ 2

/-- The original question, formalized literally as an eventual existence of a
positive constant and suitable increasing integer sequences. -/
def Question : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasManySums n c

/-- A proved sanity check: at `n = 1`, the one-term sequence `(1)` has one
represented consecutive sum, so the threshold with `c = 1` is attained.
This exercises the definitions of admissibility and represented sums. -/
theorem one_control : HasManySums 1 1 := by
  refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)), ?_, ?_⟩
  · constructor
    · intro i j hij
      have hfalse : ¬ i < j := by omega
      exact (hfalse hij).elim
    · intro i
      norm_num
  · norm_num [represented, intervalSum]

/-- The affirmative resolution recorded in the source.

SOURCE-to-formalization map: “for all sufficiently large `n`” is represented
by `∃ N, ∀ n, N ≤ n →`; “there exist integers
`a_1 < ⋯ < a_k ≤ n`” is `∃ k, ∃ a, Admissible n k a`; and “at least
`c n^2` distinct integers of the form ...” is the cardinality inequality for
`represented a`. The source records this as solved affirmatively by Beker;
the proof is not reproduced here, so this declaration has an honest proof gap. -/
theorem original_problem_solved : Question := by
  sorry

#print axioms one_control

end Erdos356
