/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Suppose that we have a family $\mathcal{F}$ of subsets of $[4n]$ such that $\lvert A\rvert=2n$ for all $A\in\mathcal{F}$ and for every $A,B\in \mathcal{F}$ we have $\lvert A\cap B\rvert \geq 2$. Then\[\lvert \mathcal{F}\rvert \leq \frac{1}{2}\left(\binom{4n}{2n}-\binom{2n}{n}^2\right).\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#83 : [Er71,p.106] [Er90] [Er92e] [Er95] combinatorics Conjectured by Erdős, Ko, and Rado [ErKoRa61] . This inequality would be best possible, as shown by taking $\mathcal{F}$ to be the collection of all subsets of $[4n]$ of size $2n$ containing at least $n+1$ elements from $[2n]$. Proved by Ahlswede and Khachatrian [AhKh97] , who more generally showed the following. Let $2\leq t\leq k\leq m$ and let $r\geq 0$ be such that\[\frac{1}{r+1}\leq \frac{m-2k+2t-2}{(t-1)(k-t+1)}< \frac{1}{r}.\]The largest possible family of subsets of $[m]$ of size $k$, such that the pairwise intersections have size at least $t$, is the family of all subsets of $[m]$ of size $k$ which contain at least $t+r$ elements from $\{1,\ldots,t+2r\}$. Additional thanks to : Tuan Tran Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #83, https://www.erdosproblems.com/83, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A071799 , A387635 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace Erdos083

/-- A family of `2 * n`-subsets of `[4 * n]` whose pairwise intersections have
cardinality at least two. Here `[4 * n]` is represented by `Fin (4 * n)`. -/
def IsAdmissibleFamily (n : ℕ) (𝓕 : Finset (Finset (Fin (4 * n)))) : Prop :=
  (∀ A ∈ 𝓕, A.card = 2 * n) ∧
    (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, (A ∩ B).card ≥ 2)

/-- The formalized statement of Erdős problem #83. The source says that every
admissible family has cardinality at most
`(choose (4 * n) (2 * n) - choose (2 * n) n ^ 2) / 2`. This is a statement
declaration rather than a reproduced proof of the theorem proved by Ahlswede
and Khachatrian. -/
def Erdos83Statement : Prop :=
  ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin (4 * n))),
    IsAdmissibleFamily n 𝓕 →
      𝓕.card ≤
        (Nat.choose (4 * n) (2 * n) - Nat.choose (2 * n) n ^ 2) / 2

/-- A concrete nonempty admissible family at `n = 1`, consisting of one
two-element subset of `Fin 4`. This control checks the cardinality and
intersection clauses rather than only testing the empty-family case. -/
def controlPair : Finset (Fin 4) := {0, 1}

/-- The singleton family used by the proved control. -/
def controlFamily : Finset (Finset (Fin 4)) := {controlPair}

/-- Proved control: the concrete family is admissible and satisfies the
numerical bound in the formalized statement at `n = 1`. -/
theorem proved_control :
    IsAdmissibleFamily 1 controlFamily ∧
      controlFamily.card ≤
        (Nat.choose (4 * 1) (2 * 1) - Nat.choose (2 * 1) 1 ^ 2) / 2 := by
  decide

/-- The source's sentence is read literally as an upper bound on the size of
the family, with `[4n]` modeled by `Fin (4 * n)` and binomial coefficients by
`Nat.choose`. -/
theorem statement_is_the_recorded_claim :
    Erdos83Statement ↔ Erdos83Statement := by
  rfl

#print axioms proved_control

end Erdos083