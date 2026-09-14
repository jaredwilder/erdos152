/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $p$ be an odd prime. Is it true that the equation\[(p-1)!+a^{p-1}=p^k\]has only finitely many solutions?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#405 : [ErGr80,p.80] number theory | factorials Erdős and Graham remark that it is probably true that in general $(p-1)!+a^{p-1}$ is rarely a power at all (although this can happen, for example $6!+2^6=28^2$). Erdős and Graham ask this allowing the case $p=2$, but this is presumably an oversight, since clearly there are infinitely many solutions to this equation when $p=2$. Brindza and Erdős [BrEr91] proved that there are finitely many such solutions. Yu and Liu [YuLi96] showed that the only solutions are\[2!+1^2=3\]\[2!+5^2=3^3\]and\[4!+1^4=5^2.\] Additional thanks to : Bhavik Mehta and Euro Sampaio Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #405, https://www.erdosproblems.com/405, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos405

/-- A positive natural-number solution of the factorial-power equation. -/
def IsPowerSolution (p a k : ℕ) : Prop :=
  Nat.Prime p ∧ 0 < a ∧ 0 < k ∧
    Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k

/-- A solution whose base prime is odd, matching the question's stated hypothesis. -/
def IsOddPrimeSolution (p a k : ℕ) : Prop :=
  IsPowerSolution p a k ∧ p % 2 = 1

/-- The three solutions recorded by the resolution, represented by `(p, a, k)`.
The use of natural numbers and positivity of `a` and `k` is the standard
interpretation of the variables in the displayed equations. -/
def KnownOddSolutions : Set (ℕ × ℕ × ℕ) :=
  {(3, 1, 1), (3, 5, 3), (5, 1, 2)}

/-- A proved sanity check: the definitions recognize the first listed solution
and reject the same prime and exponent with an incorrect power. -/
theorem solution_control :
    IsOddPrimeSolution 3 1 1 ∧ ¬ IsOddPrimeSolution 3 1 2 := by
  norm_num [IsOddPrimeSolution, IsPowerSolution]

/-- Yu and Liu's classification of the positive natural-number solutions for
odd prime `p`. This is the literature result recorded in the resolution; its
proof is not reproduced here. -/
theorem exact_odd_prime_classification :
    {s : ℕ × ℕ × ℕ | IsOddPrimeSolution s.1 s.2.1 s.2.2} =
      KnownOddSolutions := by
  sorry

/-- The question's finiteness conclusion for odd primes. This is derived from
the recorded exact classification, whose proof is imported as a literature
result above. -/
theorem finite_odd_prime_solutions :
    Set.Finite {s : ℕ × ℕ × ℕ | IsOddPrimeSolution s.1 s.2.1 s.2.2} := by
  rw [exact_odd_prime_classification]
  simp [KnownOddSolutions]

#print axioms finite_odd_prime_solutions

end Erdos405
