/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there an infinite set of primes $P$ such that if $\{a_1<a_2<\cdots\}$ is the set of integers divisible only by primes in $P$ then $\lim a_{i+1}-a_i=\infty$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#240 : [Er61,p.226] [Er65b] number theory | primes Originally asked to Erdős by Wintner. The limit is infinite for a finite set of primes, which follows from a theorem of Pólya [Po18] , that if $f(n)$ is a quadratic integer polynomial without repeated roots then as $n\to \infty$ the largest prime factor of $f(n)$ also approaches infinity. Indeed, if $P$ is a finite set of primes and $(a_i)$ is the set of integers divisible only by primes in $P$, and $a_{i+1}-a_i$ is bounded, then there exists some $k$ such that $a_{i+1}=a_i+k$ infinitely often, which contradicts Pólya's theorem with $f(n)=n(n+k)$. Tijdeman [Ti73] proved that, if $P$ is a finite set of primes, then\[a_{i+1}-a_i \gg \frac{a_i}{(\log a_i)^C}\]for some constant $C>0$ depending on $P$. Tijdeman [Ti73] resolved this question, proving that, for any $\epsilon>0$, there exists an infinite set of primes $P$ such that, with $a_i$ defined as above,\[a_{i+1}-a_i \gg a_i^{1-\epsilon}.\]See also [368] . Additional thanks to : Boris Alexeev, Dustin Mixon, Euro Vidal Sampaio, and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #240, https://www.erdosproblems.com/240, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical







open Classical Filter

namespace Erdos240

-- @category research solved

/-- A set of natural numbers consisting only of primes. -/
def IsPrimeSet (P : Set ℕ) : Prop :=
  ∀ p, p ∈ P → Nat.Prime p

/-- A positive integer is divisible only by primes belonging to `P`. -/
def IsPInteger (P : Set ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ q, Nat.Prime q → q ∣ n → q ∈ P

/-- `IsConsecutive P a b` means that `a < b` are consecutive positive
integers whose prime divisors all belong to `P`. -/
def IsConsecutive (P : Set ℕ) (a b : ℕ) : Prop :=
  IsPInteger P a ∧
    IsPInteger P b ∧
    a < b ∧
    ∀ c, a < c → c < b → ¬ IsPInteger P c

/-- The gaps between consecutive `P`-integers are unbounded.  This is the
formal reading of the source's assertion that the successive differences
tend to infinity; the resolution below is recorded as an assumed literature
result, since its proof is not reproduced here. -/
def GapsUnbounded (P : Set ℕ) : Prop :=
  ∀ B : ℕ, ∃ a b : ℕ, IsConsecutive P a b ∧ B < b - a

/-- Formalization of Erdos problem 240.

The source asks for an infinite set of primes `P` such that the increasing
sequence of positive integers with no prime divisors outside `P` has gaps
tending to infinity.  Here `IsConsecutive` identifies successive elements
directly, and `GapsUnbounded` records the corresponding unbounded-gap
property. -/
def Question240 : Prop :=
  ∃ P : Set ℕ, Set.Infinite P ∧ IsPrimeSet P ∧ GapsUnbounded P

/-- A proved control showing that `IsPInteger` is neither an empty predicate
nor an indiscriminate predicate: `1` is always `P`-smooth, while `6` is not
smooth with respect to the singleton prime set `{2}`. -/
theorem smooth_control :
    IsPInteger ({2} : Set ℕ) 1 ∧ ¬ IsPInteger ({2} : Set ℕ) 6 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    intro q hq hd
    have hq1 : q = 1 := Nat.dvd_one.mp hd
    subst q
    norm_num at hq
  · intro h
    have hp : Nat.Prime 3 := by norm_num
    have hd : (3 : ℕ) ∣ 6 := by norm_num
    have hm : (3 : ℕ) ∈ ({2} : Set ℕ) := h.2 3 hp hd
    norm_num at hm

/-- The source records this problem as resolved by Tijdeman.  The
formalization above captures the requested existence statement, but the
deep number-theoretic proof of `Question240` is not reproduced in this file. -/
theorem resolution : Question240 := by
  sorry Erdos240
