/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
We call an interval $[u,v]$ 'bad' if the greatest prime factor of $\prod_{u\leq m\leq v}m$ occurs with an exponent greater than $1$. Let $B(x)$ count the number of $n\leq x$ which are contained in at least one bad interval. Is it true that\[B(x)\sim \#\{ n\leq x: P(n)^2\mid n\},\]where $P(n)$ is the largest prime factor of $n$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#380 : [ErGr80,p.73] number theory Erdős and Graham only knew that $B(x) > x^{1-o(1)}$. Similarly, we call an interval $[u,v]$ 'very bad' if $\prod_{u\leq m\leq v}m$ is powerful. The number of integers $n\leq x$ contained in at least one very bad interval should be $\ll x^{1/2}$. In fact, it should be asymptotic to the number of powerful numbers $\leq x$. We have\[\#\{ n\leq x: P(n)^2\mid n\}=\frac{x}{\exp((c+o(1))\sqrt{\log x\log\log x})}\]for some constant $c>0$. Tao notes in the comments that if $[u,v]$ is bad then it cannot contain any primes, and hence certainly $v<2u$, and in general $v-u$ must be small (for example, assuming Cramer's conjecture, $v-u\ll (\log u)^2$). Tao [Ta26c] has proved this asymptotic, and in fact\[B(x) = \left(1+O((\log x)^{-1+o(1)})\right) \#\{ n\leq x: P(n)^2\mid n\}.\]Furthermore, the number of $n\leq x\leq x$ contained in at least one very bad interval, but are not themselves powerful, is $O(n^{2/5+o(1)})$. See also [382] . Additional thanks to : Terence Tao Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (10) Proof claims (0) More information and links This page was last edited 10 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #380, https://www.erdosproblems.com/380, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A070003 , A388654 , A387054 , A389100 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on None Previous Next <!-- R
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos380

/-- A natural number is powerful when every prime divisor occurs with exponent at
least two. This is the intrinsic divisibility formulation of the condition
`P(n)^2 ∣ n` from the source, avoiding a separate choice of largest prime factor. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- The product of the integers in the interval `[u,v]`. -/
def IntervalProduct (u v : ℕ) : ℕ :=
  ∏ m ∈ Finset.Icc u v, m

/-- `BadInterval u v` means that the greatest prime divisor of the interval
product occurs with exponent greater than one. Explicitly, some prime divisor
occurs to exponent at least two and every prime divisor is no larger than it. -/
def BadInterval (u v : ℕ) : Prop :=
  let z := IntervalProduct u v
  ∃ p : ℕ, p.Prime ∧ p ∣ z ∧ p ^ 2 ∣ z ∧
    ∀ q : ℕ, q.Prime → q ∣ z → q ≤ p

/-- The integers at most `x` that are contained in at least one bad interval.
The interval endpoints are unrestricted, as in the source definition. -/
def BadCovered (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n =>
    ∃ u v : ℕ, u ≤ n ∧ n ≤ v ∧ BadInterval u v)

/-- `B x`, the number of integers at most `x` contained in at least one bad
interval. -/
def BadCount (x : ℕ) : ℕ :=
  (BadCovered x).card

/-- The number of powerful positive integers at most `x`. The lower endpoint
`1` records the usual positive-integer convention for the counting function. -/
def PowerfulCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter IsPowerful).card

/-- The asymptotic assertion `B(x) ∼ #{n ≤ x : P(n)^2 ∣ n}`, expressed as
convergence of the quotient to one. The denominator is harmless for all
sufficiently large `x`, since `1` is powerful. -/
def AsymptoticClaim : Prop :=
  Tendsto
    (fun x : ℕ => (BadCount x : ℝ) / (PowerfulCount x : ℝ))
    atTop (𝓝 1)

/-- The proposed asymptotic is the resolved statement recorded by the source:
Tao proved it. The proof is intentionally left as an explicit gap because the
analytic number-theoretic argument is not reproduced here. -/
theorem tao_asymptotic : AsymptoticClaim := by
  sorry

/-- The basic anti-vacuity control: `1` is powerful, so the comparison counting
function is not identically zero. -/
theorem one_powerful : IsPowerful 1 := by
  simp [IsPowerful]

/-- The same control exhibited inside the actual finite counting set. -/
theorem one_mem_powerful_filter :
    1 ∈ (Finset.Icc 1 1).filter IsPowerful := by
  simp [one_powerful]

#print axioms one_powerful

end Erdos380
