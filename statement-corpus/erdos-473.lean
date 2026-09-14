/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there a permutation $a_1,a_2,\ldots$ of the positive integers such that $a_k+a_{k+1}$ is always prime?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#473 : [ErGr80,p.94] number theory Asked by Segal. The answer is yes, as shown by Odlyzko (although no reference is given). Watts has suggested that perhaps the obvious greedy algorithm defines such a permutation - that is, let $a_1=1$ and let\[a_{n+1}=\min \{ x : a_n+x\textrm{ is prime and }x\neq a_i\textrm{ for }i\leq n\}.\]In other words, do all positive integers occur as some such $a_n$? Do all primes occur as a sum? In the comments van Doorn has noted that the answer to the latter question is no, since $197$ does not appear as a sum from such a greedy sequence. In [ErGr80] they also note that Segal asked the finite version: is there, for all $n\geq 2$, a permutation $a_1,\ldots,a_n$ of $\{1,\ldots,n\}$ such that $a_k+a_{k+1}$ is prime for $1\leq k<n$. The answer is likely yes on probabilistic grounds, and is true for infinitely many $n$ (see this discussion ). Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 02 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #473, https://www.erdosproblems.com/473, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A055265 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos473

/-- A sequence indexed by `ℕ` is a permutation of the positive integers when every
value is positive, values are distinct, and every positive integer occurs. -/
def PositivePermutation (a : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ Function.Injective a ∧
    (∀ m, 0 < m → ∃ n, a n = m)

/-- The adjacent-prime condition for a zero-indexed sequence; index `k` corresponds
to the source's `a_{k+1}`. -/
def PrimeAdjacent (a : ℕ → ℕ) : Prop :=
  ∀ k, Nat.Prime (a k + a (k + 1))

/-- Formalization of the question in the source: does there exist a permutation of
the positive integers whose consecutive sums are prime? -/
def Question : Prop :=
  ∃ a : ℕ → ℕ, PositivePermutation a ∧ PrimeAdjacent a

/-- The canonical enumeration `n ↦ n+1` satisfies the permutation part of the
formalization, so that predicate is not vacuous. -/
theorem canonical_positive_permutation :
    PositivePermutation (fun n : ℕ => n + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    omega
  · intro x y h
    omega
  · intro m hm
    have hm1 : 1 ≤ m := by
      omega
    refine ⟨m - 1, ?_⟩
    dsimp
    omega

/-- The adjacent-prime predicate itself has a simple positive example, namely the
constant sequence with value `1`; this control does not assert that it is a
permutation. -/
theorem constant_one_prime_adjacent :
    PrimeAdjacent (fun _ : ℕ => 1) := by
  intro k
  simpa using Nat.prime_two

/-- The canonical positive permutation is not an accidental solution to the
adjacent-prime condition: at index `3` it produces the non-prime sum `4+5=9`. -/
theorem canonical_not_prime_adjacent :
    ¬ PrimeAdjacent (fun n : ℕ => n + 1) := by
  intro h
  have h3 := h 3
  norm_num at h3

#print axioms canonical_positive_permutation
#print axioms constant_one_prime_adjacent
#print axioms canonical_not_prime_adjacent

/-- The resolution records that the answer to the main existence question is yes,
attributed to Odlyzko. The formal proof of that resolved number-theoretic result
remains to be supplied here. -/
theorem answer_is_yes : Question := by
  sorry Erdos473
