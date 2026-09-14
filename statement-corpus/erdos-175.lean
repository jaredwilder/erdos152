/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Show that, for any $n\geq 5$, the binomial coefficient $\binom{2n}{n}$ is not squarefree.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#175 : [Er79,p.67] [ErGr80,p.71] number theory | binomial coefficients It is easy to see that $4\mid \binom{2n}{n}$ except when $n=2^k$, and hence it suffices to prove this when $n$ is a power of $2$. Proved by Sárközy [Sa85] for all sufficiently large $n$, and independently by Granville and Ramaré [GrRa96] and Velammal [Ve95] for all $n\geq 5$. More generally, if $f(n)$ is the largest integer such that, for some prime $p$, we have $p^{f(n)}$ dividing $\binom{2n}{n}$, then $f(n)$ should tend to infinity with $n$. Can one even disprove that $f(n)\gg \log n$? Sander [Sa92] proved that $f(n)\to \infty$, and later [Sa95] quantified this to $f(n) \gg (\log n)^{1/10-o(1)}$. Sander [Sa95] also proved that $f(n)\ll \log n$ for all $n$, and that $f(n) \gg \log n$ for almost all $n$. The proofs of the latter two facts are very easy using Kummer's theorem -- indeed, this immediately implies that any $p$ divides $\binom{2n}{n}$ with multiplicity $\ll \log_p n$, and that the multiplicity with which $2$ divides $\binom{2n}{n}$ is equal to the number of $1$s in the binary expansion of $n$, which is $\gg \log n$ for almost all $n$. Erdős and Kolesnik [ErKo99] improved the lower bound for all $n$ to\[f(n) \gg (\log n)^{1/4-o(1)}.\]It remains open whether $f(n) \gg \log n$ for all $n$. Sander [Sa92b] proved that, for all $0<\epsilon<1$, if $n$ is sufficiently large and $\lvert d\rvert\leq n^{1-\epsilon}$ then $\binom{2n+d}{n}$ is not squarefree. The largest $n$ known for which $\binom{2n}{n}$ is not divisible by the square of an odd prime is $n=786$ (found by Levine). Guy [Gu04] reports that Erdős 'feels sure that there are no larger such $n$'. See also [379] . This is mentioned in problem B33 of Guy's collection [Gu04] . Additional thanks to : Boris Alexeev, Alfaiz, Hung Bui, and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (4) Proof claims (0) More information and links This page was last edited 08 February 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #175, https://www.erdosproblems.com/175, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos175

/-- A natural number is squarefree when no square of a prime divides it. -/
def IsSquarefreeNat (m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ m

/-- The central binomial coefficient appearing in Erdős Problem 175. -/
def centralBinomial (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n

/-- A proved computation showing that the formalized central binomial coefficient is
nontrivial at the smallest numerical control value. -/
theorem central_binomial_at_five :
    centralBinomial 5 = 252 := by
  decide

/-- A proved local control: the concrete value `252` is not squarefree, since the
square of the prime `2` divides it. -/
theorem not_squarefree_252 : ¬ IsSquarefreeNat 252 := by
  intro h
  have hp : Nat.Prime 2 := by
    norm_num
  have hd : (2 : ℕ) ^ 2 ∣ 252 := by
    norm_num
  exact (h 2 hp) hd

/-- A proved control connecting the concrete computation with the squarefreeness
predicate used in the main statement. -/
theorem central_binomial_five_not_squarefree :
    ¬ IsSquarefreeNat (centralBinomial 5) := by
  rw [central_binomial_at_five]
  exact not_squarefree_252

/-- The resolved statement of Erdős Problem 175: for every natural number `n` at
least five, the central binomial coefficient is not squarefree. The proof of the
general theorem is not reproduced here; the remaining gap is the substantive
number-theoretic argument established in the cited references. -/
theorem central_binomial_not_squarefree
    (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSquarefreeNat (centralBinomial n) := by
  sorry

#print axioms central_binomial_at_five
#print axioms not_squarefree_252
#print axioms central_binomial_five_not_squarefree

end Erdos175
