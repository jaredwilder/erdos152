/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a prime $p<n/2$ (except $\binom{7}{3}=5\cdot 7$).

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#384 : [ErGr80,p.73] number theory | binomial coefficients A conjecture of Erdős and Selfridge. Proved by Ecklund [Ec69] , who made the stronger conjecture that whenever $n>k^2$ the binomial coefficient $\binom{n}{k}$ is divisible by a prime $p<n/k$. They have proved the weaker inequality $p\ll n/k^c$ for some constant $c>0$. Discussed in problem B31 and B33 of Guy's collection [Gu04] - there Guy credits Selfridge with the conjecture that if $n> 17.125k$ then $\binom{n}{k}$ has a prime factor $p\leq n/k$. Stronger forms of this conjecture are [1094] and [1095] . Additional thanks to : Zachary Chase Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 28 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #384, https://www.erdosproblems.com/384, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos384

/-- `HasSmallPrimeFactor n k` means that the binomial coefficient
`Nat.choose n k` has a prime divisor `p` satisfying the literal natural-number
translation `2 * p < n` of `p < n / 2`. -/
def HasSmallPrimeFactor (n k : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ 2 * p < n ∧ p ∣ Nat.choose n k

/-- The exceptional binomial coefficient in the source really is
`binom 7 3 = 35 = 5 * 7`. -/
theorem exceptional_value : Nat.choose 7 3 = 35 := by
  norm_num [Nat.choose]

/-- Anti-vacuity control: the exceptional pair `(7,3)` does not have a prime
factor satisfying the strict bound `2 * p < 7`. -/
theorem exceptional_control : ¬ HasSmallPrimeFactor 7 3 := by
  intro h
  rcases h with ⟨p, hp, hlt, hdiv⟩
  have hple : p ≤ 3 := by
    omega
  have hcases : p = 2 ∨ p = 3 := by
    have htwo : 2 ≤ p := hp.two_le
    omega
  have hchoose : Nat.choose 7 3 = 35 := exceptional_value
  rw [hchoose] at hdiv
  rcases hcases with rfl | rfl <;> norm_num at hdiv

/-- Erdős's and Selfridge's binomial-coefficient assertion, as recorded in
Erdős Problem #384.

The source sentence reads: if `1 < k < n - 1`, then `binom n k` is divisible
by a prime `p < n/2`, except for `(n,k) = (7,3)`.  Here `2 * p < n` is used
to express that strict inequality without the rounding ambiguity of natural
division.  The source resolution records this result as proved by Ecklund;
the proof of this deep theorem is not supplied here. -/
theorem erdos_384 :
    ∀ n k : ℕ,
      1 < k →
      k < n - 1 →
      (n = 7 ∧ k = 3) ∨ HasSmallPrimeFactor n k := by
  sorry

#print axioms exceptional_control

end Erdos384
