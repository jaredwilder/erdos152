/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $n=p^2+p+1$ for some prime power $p$, and let $A_1,\ldots,A_t\subseteq \{1,\ldots,n\}$ be a block design (so that every pair $x,y\in \{1,\ldots,n\}$ is contained in exactly one $A_i$). Is it true that if $t>n$ then $t\geq n+p$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#903 : [Er82e] combinatorics A conjecture of Erdős and Sós. The classic finite geometry construction shows that $t=n$ is possible. A theorem of Erdős and de Bruijn [dBEr48] states that $t\geq n$. This is true, and was proved by Erdős, Fowler, Sós, and Wilson [EFSW85] , who further show that unless the block design is obtained from a projective plane by 'breaking up' one of its lines then $t\geq n+cp$ where $c\approx 1.148$. In general, one can ask what the possible values of $t$ are, for a given $n$. Additional thanks to : Mark Sellke Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 24 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #903, https://www.erdosproblems.com/903, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos903

/-- The parameter `p` is a prime power, with positive exponent. -/
def IsPrimePower (p : ℕ) : Prop :=
  2 ≤ p ∧ ∃ q k : ℕ, Nat.Prime q ∧ p = q ^ (k + 1)

/-- POSITIVE WITNESS: `2` is a prime power. -/
theorem IsPrimePower_witness_pos : IsPrimePower 2 := by
  refine ⟨by norm_num, 2, 0, by norm_num, by norm_num⟩

/-- NEGATIVE WITNESS: `1` is a near-miss prime-power parameter, failing the lower bound. -/
theorem IsPrimePower_witness_neg : ¬ IsPrimePower 1 := by
  intro h
  omega

/-- A finite block design on `Fin n`: every pair of distinct points lies in exactly
one block among the `t` blocks. -/
def IsBlockDesign (n t : ℕ) (A : Fin t → Finset (Fin n)) : Prop :=
  ∀ x y : Fin n, x ≠ y → ∃! i : Fin t, x ∈ A i ∧ y ∈ A i

/-- POSITIVE WITNESS: the three two-point subsets of a three-point set form a block design. -/
theorem IsBlockDesign_witness_pos :
    IsBlockDesign 3 3
      (![({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)),
        ({1, 2} : Finset (Fin 3))]) := by
  decide

/-- NEGATIVE WITNESS: removing one block from the positive example leaves the pair
`1,2` uncovered, so this is a near miss violating exactly one covering condition. -/
theorem IsBlockDesign_witness_neg :
    ¬ IsBlockDesign 3 3
      (![({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), (∅ : Finset (Fin 3))]) := by
  decide

/-- The finite bounded version of prime-power recognition, restricted to bases and
exponents below `B`; this is decidable on finite instances. -/
def IsPrimePowerFinite (p B : ℕ) : Prop :=
  2 ≤ p ∧ ∃ q k : Fin B, q.1.Prime ∧ p = q.1 ^ (k.1 + 1)

/-- POSITIVE WITNESS: `2` is recognized as a prime power with bound `3`. -/
theorem IsPrimePowerFinite_witness_pos : IsPrimePowerFinite 2 3 := by
  decide

/-- NEGATIVE WITNESS: `1` is the near-miss parameter excluded by the lower bound. -/
theorem IsPrimePowerFinite_witness_neg : ¬ IsPrimePowerFinite 1 3 := by
  decide

/-- Erdős problem #903.  The source clause is “if `t > n` then `t ≥ n + p`”,
with `n = p^2 + p + 1`; the block-design hypothesis is formalized by
`IsBlockDesign n t A`.  The resolution records this assertion as proved, but
the proof is not reproduced here. -/
theorem erdos903 :
    ∀ p t : ℕ, IsPrimePower p →
      ∀ A : Fin t → Finset (Fin (p * p + p + 1)),
        IsBlockDesign (p * p + p + 1) t A →
        t > p * p + p + 1 →
        t ≥ p * p + 2 * p + 1 := by
  sorry Erdos903
