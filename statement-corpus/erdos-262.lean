/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Suppose $a_1<a_2<\cdots$ is a sequence of integers such that for all integer sequences $t_n$ with $t_n\geq 1$ the sum\[\sum_{n=1}^\infty \frac{1}{t_na_n}\]is irrational. How slowly can $a_n$ grow?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#262 : [ErGr80,p.63] [Er88c,p.105] irrationality One possible definition of an 'irrationality sequence' (see also [263] and [264] ). An example of such a sequence is $a_n=2^{2^n}$ (proved by Erdős [Er75c] ), while a non-example is $a_n=n!$. It is known that if $a_n$ is such a sequence then $a_n^{1/n}\to\infty$. This was essentially solved by Hančl [Ha91] , who proved that such a sequence needs to satisfy\[\limsup_{n\to \infty} \frac{\log_2\log_2 a_n}{n} \geq 1.\]More generally, if $a_n\ll 2^{2^{n-F(n)}}$ with $F(n)<n$ and $\sum 2^{-F(n)}<\infty$ then $a_n$ cannot be an irrationality sequence. Additional thanks to : Vjekoslav Kovac and Terence Tao Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 28 September 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #262, https://www.erdosproblems.com/262, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos262

/-- An irrationality sequence in the natural-number encoding.

The source uses positive integer sequences indexed from `1`.  We use indices in
`ℕ`, require positivity explicitly, and encode the assertion that every
allowed reciprocal series is summable and has an irrational real sum. -/
def IrrationalitySequence (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
    (∀ n, 0 < a n) ∧
      ∀ t : ℕ → ℕ, (∀ n, 1 ≤ t n) →
        Summable (fun n => (1 : ℝ) / ((t n : ℝ) * (a n : ℝ))) ∧
          Irrational (∑' n, (1 : ℝ) / ((t n : ℝ) * (a n : ℝ)))

/-- A direct formalization of the lower-growth conclusion
`limsup (log₂ log₂ aₙ) / n ≥ 1`, expressed without extended-real
`limsup`: every threshold below `1` is attained arbitrarily far out.

The logarithms here are `Nat.log`, so this is an explicit discrete
interpretation of the source's base-two logarithms. -/
def HanclLowerBound (a : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ 0 < n ∧
        1 - ε ≤
          (Nat.log 2 (Nat.log 2 (a n)) : ℝ) / (n : ℝ)

/-- A proved control showing that the strict-monotonicity component is
non-vacuous: the sequence `n ↦ n + 1` is strictly increasing. -/
theorem strictMono_succ_sequence : StrictMono (fun n : ℕ => n + 1) := by
  intro m n h
  omega

/-- A proved control extracting strict increase from the definition of an
irrationality sequence. -/
theorem irrationalitySequence_strictMono
    {a : ℕ → ℕ} (h : IrrationalitySequence a) : StrictMono a :=
  h.1

/-- A proved control extracting positivity from the definition of an
irrationality sequence. -/
theorem irrationalitySequence_positive
    {a : ℕ → ℕ} (h : IrrationalitySequence a) (n : ℕ) : 0 < a n :=
  h.2.1 n

/-- The Erdős example `aₙ = 2^(2^n)` is an irrationality sequence.
This is the theorem proved by Erdős cited in the frozen resolution; its
substantial analytic and irrationality proof remains an explicit formalization
gap here. -/
theorem dyadic_is_irrationalitySequence :
    IrrationalitySequence (fun n : ℕ => 2 ^ (2 ^ n)) := by
  sorry

/-- Hančl's resolved lower bound for irrationality sequences, in the
discrete `HanclLowerBound` formulation above.  The proof of this literature
result is not reproduced here and remains an explicit formalization gap. -/
theorem hancl_lower_bound
    {a : ℕ → ℕ} (h : IrrationalitySequence a) :
    HanclLowerBound a := by
  sorry

#print axioms strictMono_succ_sequence
#print axioms irrationalitySequence_strictMono
#print axioms irrationalitySequence_positive

end Erdos262
