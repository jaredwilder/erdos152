/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\alpha\geq 1$. Is there a sequence of integers $n_k,m_k$ such that $n_k/m_k\to \alpha$ and $\sigma(n_k)=\sigma(m_k)$ for all $k\geq 1$, where $\sigma$ is the sum of divisors function?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#823 : [Er59c] [Er74b] number theory Erdős [Er74b] writes it is 'easy to prove the analogous result for $\phi(n)$. The answer is yes, proved by Pollack [Po15b] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 28 September 2025. ( View history ) View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #823, https://www.erdosproblems.com/823, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos823

/-- The sum of the positive divisors of `n`, computed by testing all numbers up to `n`.
The convention is that the source's positive integers are represented by natural numbers
and positivity is imposed on the sequence terms. -/
def divisorSum (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (n + 1), if n % d = 0 then d else 0

/-- POSITIVE WITNESS: the divisor sums of `6` and `11` agree. -/
theorem divisorSum_witness_pos : divisorSum 6 = 12 ∧ divisorSum 11 = 12 := by
  decide

/-- NEGATIVE WITNESS: `5` is a near-miss for the divisor-sum value at `6`. -/
theorem divisorSum_witness_neg : divisorSum 5 ≠ 12 := by
  decide

/-- The original question, read with positive natural-number sequences:
there is a sequence whose quotients tend to every real `α ≥ 1`, while the
corresponding divisor sums agree term by term. -/
def ErdosQuestion : Prop :=
  ∀ α : ℝ, 1 ≤ α →
    ∃ n m : ℕ → ℕ,
      (∀ k : ℕ, 1 ≤ n k ∧ 1 ≤ m k) ∧
      Tendsto (fun k : ℕ => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 α) ∧
      ∀ k : ℕ, divisorSum (n k) = divisorSum (m k)

/-- A bounded, decidable finite-instance version of the question: `n` and `m`
are required to lie among the first `N` positive natural numbers, have the
specified quotient `a / b`, and have equal divisor sums. -/
def QuestionFinite (N a b n m : ℕ) : Prop :=
  1 ≤ n ∧ n < N ∧
  1 ≤ m ∧ m < N ∧
  1 ≤ b ∧
  b * n = a * m ∧
  divisorSum n = divisorSum m

/-- POSITIVE WITNESS: `6/11` is realized by the equal-divisor-sum pair
`(6,11)` among the first twelve positive natural numbers. -/
theorem questionFinite_witness_pos :
    QuestionFinite 12 6 11 6 11 := by
  decide

/-- NEGATIVE WITNESS: reversing the pair preserves the divisor-sum equality
but breaks the specified quotient, so this is a one-condition near miss. -/
theorem questionFinite_witness_neg :
    ¬ QuestionFinite 12 6 11 11 6 := by
  decide

/-- COMPUTED CONTROL: the finite predicate is genuinely nontrivial on nearby
explicit instances, not merely an unfolding tautology. -/
theorem questionFinite_control :
    QuestionFinite 12 6 11 6 11 ∧ ¬ QuestionFinite 12 6 11 11 6 := by
  exact ⟨questionFinite_witness_pos, questionFinite_witness_neg⟩

/-- Pollack's result, as recorded in the resolution node, establishes that the
answer to the original question is yes. The proof is not reproduced here;
this declaration is an explicit literature input and therefore remains a
`sorry` gap rather than an invented axiom. -/
theorem pollack_answer : ErdosQuestion := by
  sorry

#print axioms divisorSum_witness_pos
#print axioms divisorSum_witness_neg
#print axioms questionFinite_witness_pos
#print axioms questionFinite_witness_neg
#print axioms questionFinite_control
#print axioms pollack_answer

end Erdos823
