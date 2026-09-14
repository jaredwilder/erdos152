/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that for almost all $n$ there exists some $m\in (p_n,p_{n+1})$ such that\[p(m) \geq p_{n+1}-p_n,\]where $p(m)$ denotes the least prime factor of $m$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#682 : [Er79d] number theory | primes Erdős first thought this should be true for all large $n$, but found a (conditional) counterexample: Dickson's conjecture says there are infinitely many $d$ such that\[2183+30030d\textrm{ and }2201+30030d\]are both prime, and then they must necessarily be consecutive primes. These give a counterexample since $30030=2\cdot 3 \cdot 5\cdot 7\cdot 11\cdot 13$ and every integer in $[2184,2200]$ is divisible by at least one of these primes. This was solved in the affirmative by Gafni and Tao [GaTa25] , who proved that the number of exceptional $n\in [1,X]$ is\[\ll \frac{X}{(\log X)^2},\]and proved, conditional on a form of the prime tuples conjecture, that the number of exceptional $n\in[1,X]$ satisifes\[\sim c\frac{X}{(\log X)^2}\]for some explicit $c>0$. See also [680] and [681] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #682, https://www.erdosproblems.com/682, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A386978 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos682

/-!
We interpret “almost all” as density one: the exceptional counting function is
required to be `o(X)`.  The quantitative estimate recorded in the resolution
is stronger than this interpretation.
-/

/-- The `n`th prime, with indexing beginning at `n = 0`. -/
noncomputable def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- The least prime factor of a natural number, using `Nat.minFac`'s convention
at `0` and `1`. -/
def leastPrimeFactor (m : ℕ) : ℕ :=
  Nat.minFac m

/-- The gap between the primes at indices `n` and `n + 1`. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  primeAt (n + 1) - primeAt n

/-- An index is good when there is an integer strictly between the two
successive primes for which the least prime factor is at least their gap. -/
noncomputable def GoodIndex (n : ℕ) : Prop :=
  ∃ m : ℕ,
    primeAt n < m ∧
    m < primeAt (n + 1) ∧
    leastPrimeFactor m ≥ primeGap n

/-- The number of exceptional indices in the interval `[1, X]`. -/
noncomputable def exceptionalCount (X : ℕ) : ℕ :=
  (Finset.filter (fun n : ℕ => 1 ≤ n ∧ ¬ GoodIndex n)
    (Finset.range (X + 1))).card

/-- A set of natural-number indices has density zero when its counting function
is eventually bounded by every positive rational multiple of `X`. -/
def HasDensityZero (count : ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (count X : ℚ) ≤ ε * (X : ℚ)

/-- The formal version of “for almost all `n` there exists such an `m`”:
the exceptional indices have density zero. -/
def Question : Prop :=
  HasDensityZero exceptionalCount

/-- A proved sanity check for the least-prime-factor definition: the least
prime factor of `15` is `3`. -/
theorem least_prime_factor_control :
    leastPrimeFactor 15 = 3 := by
  norm_num [leastPrimeFactor]

/-- A proved sanity check for the exceptional counting function at `X = 0`;
the lower bound `1 ≤ n` excludes the sole index in `Finset.range 1`. -/
theorem exceptional_count_zero :
    exceptionalCount 0 = 0 := by
  simp [exceptionalCount]

/-- The affirmative resolution of Erdős Problem 682.  The source says that
the number of exceptional `n ≤ X` is `≪ X / (log X)^2`, which implies the
density-zero formulation used here.  The analytic result of Gafni and Tao is
not reproved in this file; this theorem records that external result as an
honest formalization gap.

The source clause reads: “for almost all `n` there exists some `m` in
`(p_n,p_{n+1})` such that `p(m) ≥ p_{n+1} - p_n`”.  Here `primeAt n`
represents `p_n`, `leastPrimeFactor m` represents `p(m)`, and `GoodIndex n`
is exactly the displayed existential condition. -/
theorem question_answer : Question := by
  sorry Erdos682
