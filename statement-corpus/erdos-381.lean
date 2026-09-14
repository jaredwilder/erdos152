/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
A number $n$ is highly composite if $\tau(m)<\tau(n)$ for all $m<n$, where $\tau(m)$ counts the number of divisors of $m$. Let $Q(x)$ count the number of highly composite numbers in $[1,x]$. Is it true that\[Q(x)\gg_k (\log x)^k\]for every $k\geq 1$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#381 : [Er44] number theory | divisors Erdős [Er44] proved $Q(x)\gg (\log x)^{1+c}$ for some constant $c>0$. The answer to this problem is no: Nicolas [Ni71] proved that\[Q(x) \ll (\log x)^{O(1)}.\] Additional thanks to : Julius Schmerling Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #381, https://www.erdosproblems.com/381, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A002182 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos381

/-- The number of positive divisors of `n`, computed by filtering the possible
divisors below `n + 1`. -/
def divisorCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun d => d ∣ n) |>.card

/-- `n` is highly composite when it is positive and has strictly more divisors
than every smaller positive natural number. The positivity condition excludes
the vacuous endpoint `n = 0`, which is not a positive integer in the source's
definition. -/
def highlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → divisorCount m < divisorCount n

/-- The counting function `Q(x)`, represented as the cardinality of the finite
set of highly composite numbers in the interval `[1,x]`. -/
noncomputable def highlyCompositeCount (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter highlyComposite |>.card

/-- A precise natural-number encoding of the source's notation
`Q(x) ≫_k (log x)^k`: for every positive exponent there is a positive real
constant and a threshold after which the corresponding lower bound holds.
The logarithm is represented by the base-two natural logarithm; this is an
explicit discrete encoding of the asymptotic statement. -/
def PolylogLowerBound : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (highlyCompositeCount x : ℝ) ≥
          c * (Nat.log 2 x : ℝ) ^ k

/-- The question from the source, after encoding its asymptotic notation as
`PolylogLowerBound`. The source resolution records that this proposition is
false; the proof of that negative result is not reproduced here. -/
def Question : Prop :=
  PolylogLowerBound

/-- A proved control showing that the divisor-counting definition is not
constant: `1` has one positive divisor. -/
theorem divisorCount_one : divisorCount 1 = 1 := by
  decide

/-- A proved control showing that the divisor-counting definition is not
constant: `2` has two positive divisors. -/
theorem divisorCount_two : divisorCount 2 = 2 := by
  decide

/-- A proved control exercising the highly-composite predicate at its first
positive value. -/
theorem highlyComposite_one : highlyComposite 1 := by
  refine ⟨by decide, ?_⟩
  intro m hm hlt
  omega

/-- A proved control exercising the highly-composite predicate at `2`. -/
theorem highlyComposite_two : highlyComposite 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm hlt
  have hm1 : m = 1 := by
    omega
  subst m
  decide

/-- The count at the empty interval is zero, providing a sanity check for the
definition of `highlyCompositeCount`. -/
theorem highlyCompositeCount_zero : highlyCompositeCount 0 = 0 := by
  simp [highlyCompositeCount, highlyComposite]

/-- The source resolution says the answer is no: Nicolas proved an upper
polylogarithmic bound, contradicting the assertion that the lower bound holds
for every exponent. A complete formal proof of this analytic number-theoretic
result remains to be supplied here. -/
theorem answer_is_no : ¬ Question := by
  sorry

#print axioms divisorCount_one
#print axioms divisorCount_two
#print axioms highlyComposite_one
#print axioms highlyComposite_two
#print axioms highlyCompositeCount_zero
