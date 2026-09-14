/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A=\{a_1<\cdots<a_t\}\subseteq \{1,\ldots,N\}$ be such that $\phi(a_1)<\cdots<\phi(a_t)$. The primes are such an example. Are they the largest possible? Can one show that $\lvert A\rvert<(1+o(1))\pi(N)$ or even $\lvert A\rvert=o(N)$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#49 : [Er95] [Er95c] number theory | primes Erdős remarks that the last conjecture is probably easy, and that similar questions can be asked about $\sigma(n)$. Solved by Tao [Ta24d] , who proved that\[ \lvert A\rvert \leq \left(1+O\left(\frac{(\log\log x)^5}{\log x}\right)\right)\pi(x).\]In [Er95c] Erdős further asks about the situation when $\phi(a_1)\leq \cdots \leq \phi(a_t)$. See also [415] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 19 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #49, https://www.erdosproblems.com/49, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A365339 , A365474 Reactions Likes holyterror Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem49

/-- The number of primes at most `N`, used as a formal counterpart of `π(N)`. -/
def primeCount (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime |>.card

/-- `admissible φ N A` formalizes the source condition: `A` is contained in
`{1, ..., N}`, and `φ` is strictly increasing on the elements of `A` in their
usual order. -/
def admissible (φ : ℕ → ℕ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a < b → φ a < φ b

/-- The first asymptotic alternative asked for in the source, with `φ` fixed
to Euler's totient function. -/
def firstAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, admissible Nat.totient N A →
        (A.card : ℝ) ≤ (1 + ε) * (primeCount N : ℝ)

/-- The stronger little-oh alternative asked for in the source. -/
def sublinear : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, admissible Nat.totient N A →
        (A.card : ℝ) ≤ ε * (N : ℝ)

/-- The formalized question is the disjunction of the two asymptotic bounds
asked in the source. The source asks whether `A` can be bounded by
`(1+o(1))π(N)`, or even by `o(N)`; these are represented by
`firstAsymptotic` and `sublinear`, respectively. -/
def question : Prop :=
  firstAsymptotic ∨ sublinear

/-- Every admissible set is contained in the finite interval represented by
`range (N+1)`, hence its cardinality is at most `N+1`. This is a proved
sanity control for the formalized admissibility condition. -/
theorem admissible_card_le (φ : ℕ → ℕ) (N : ℕ) (A : Finset ℕ)
    (hA : admissible φ N A) : A.card ≤ N + 1 := by
  have hsub : A ⊆ Finset.range (N + 1) := by
    intro a ha
    have haIcc : a ∈ Finset.Icc 1 N := hA.1 ha
    have haN : a ≤ N := (Finset.mem_Icc.mp haIcc).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le haN)
  exact Finset.card_le_card hsub

/-- The empty set satisfies the source's finite admissibility condition. -/
theorem empty_admissible (φ : ℕ → ℕ) (N : ℕ) :
    admissible φ N ∅ := by
  constructor
  · intro a ha
    simp at ha
  · intro a b ha hb hab
    simp at ha

/-- Tao's result, as recorded in the resolution node, is represented by the
usual quantified meaning of the displayed `O`-term. This is an external
literature theorem input: the present file formalizes its statement and
checks consequences of the definitions, but does not reproduce Tao's proof. -/
def taoBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, admissible Nat.totient N A →
        (A.card : ℝ) ≤
          (1 + C *
            ((Real.log (Real.log (N : ℝ))) ^ 5 / Real.log (N : ℝ))) *
            (primeCount N : ℝ)

/-- The resolution recorded by the source, namely Tao's asymptotic estimate. -/
axiom tao_resolution : taoBound

#print axioms admissible_card_le
#print axioms empty_admissible
#print axioms tao_resolution

end ErdosProblem49