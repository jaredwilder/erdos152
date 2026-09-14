/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $f(n)$ be minimal such that there is an intersecting family $\mathcal{F}$ of sets of size $n$ (so $A\cap B\neq\emptyset$ for all $A,B\in \mathcal{F}$) with $\lvert \mathcal{F}\rvert=f(n)$ such that any set $S$ with $\lvert S\rvert \leq n-1$ is disjoint from at least one $A\in\mathcal{F}$. Is it true that\[f(n) \ll n?\]
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#21 : [Er81] [Er90] [Er92b] [Er97f] combinatorics | intersecting family Conjectured by Erdős and Lovász [ErLo75] , who proved that\[\frac{8}{3}n-3\leq f(n) \ll n^{3/2}\log n\]for all $n$. The upper bound was improved by Kahn [Ka92b] to\[f(n) \ll n\log n.\](The upper bound constructions in both cases are formed by taking a random set of lines from a projective plane of order $n-1$, assuming $n-1$ is a prime power.) This problem was solved by Kahn [Ka94] who proved the upper bound $f(n) \ll n$. The Erdős-Lovász lower bound of $\frac{8}{3}n-O(1)$ has not been improved, and it has been speculated (see e.g. [Ka94] ) that the correct answer is $3n+O(1)$. It is trivial that $f(1)=1$ and $f(2)=3$. The values $f(3)=6$ and $f(4)=9$ were established by Tripathi [Tr14] . Barát and Wanless [BaWa21] proved that $f(5)=13$, and that $13\leq f(6)\leq 18$. Additional thanks to : Noga Alon, Zachary Chase, and Alexis Olson Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 03 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #21, https://www.erdosproblems.com/21, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A391599 Reactions Likes holyterror Open to collaboration None Currently working on None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem21

/-- A finite family of finite sets of natural numbers is admissible at parameter `n`
when all its members have size `n`, its members pairwise intersect, and every set
of size at most `n - 1` misses at least one member of the family. -/
def Admissible (n : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ 𝓕, A.card = n) ∧
  (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, (A ∩ B).Nonempty) ∧
  (∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ 𝓕, Disjoint S A)

/-- The literal extremal quantity in the source: the infimum of the cardinalities
of admissible intersecting families of `n`-sets. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ 𝓕 : Finset (Finset ℕ), Admissible n 𝓕 ∧ 𝓕.card = k}

/-- The asymptotic assertion represented by the source's notation `f(n) ≪ n`. -/
def LinearBound : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ C * n

/-- The question from the source, formalized as the eventual linear upper-bound
assertion. The resolution records that this assertion is true, but this file
keeps the question as a proposition rather than incorrectly presenting the
literature result as a proved Lean theorem. -/
def Question : Prop :=
  LinearBound

/-- A singleton consisting of the one-element set `{0}` is admissible at `n = 1`. -/
theorem singleton_one_admissible :
    Admissible 1 ({({0} : Finset ℕ)} : Finset (Finset ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    simp at hA
    simpa [hA]
  · intro A hA B hB
    simp at hA hB
    subst A
    subst B
    simp
  · intro S hS
    have hzero : S.card = 0 := by
      omega
    have hempty : S = ∅ := Finset.card_eq_zero.mp hzero
    subst S
    exact ⟨{0}, by simp, by simp⟩

/-- A proved control exercising the extremal definition: the literal quantity
satisfies `f 1 ≤ 1`, witnessed by the singleton family from the preceding
lemma. -/
theorem f_one_le_one : f 1 ≤ 1 := by
  apply Nat.sInf_le
  refine ⟨({({0} : Finset ℕ)} : Finset (Finset ℕ)), singleton_one_admissible, ?_⟩
  simp

#print axioms singleton_one_admissible
#print axioms f_one_le_one

end ErdosProblem21