/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $c<1$ be some constant and $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ be such that $\lvert A_i\rvert >c\sqrt{n}$ for all $i$ and $\lvert A_i\cap A_j\rvert\leq 1$ for all $i\neq j$. Must there exist some set $B$ such that $B\cap A_i\neq \emptyset$ and $\lvert B\cap A_i\rvert \ll_c 1$ for all $i$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#664 : [Er81] [Er97f] combinatorics This would imply in particular that in a finite geometry there is always a blocking set which meets every line in $O(1)$ many points. In [Er81] the condition $\lvert A_i\cap A_j\rvert\leq 1$ for all $i\neq j$ is replaced by every two points in $\{1,\ldots,n\}$ being contained in exactly one $A_i$, that is, $A_1,\ldots,A_m$ is a pairwise balanced block design (and the condition $c<1$ is omitted). Alon has proved that the answer is no: if $q$ is a large prime power and $n=m=q^2+q+1$ then there exist $A_1,\ldots,A_m\subseteq \{1,\ldots,n\}$ such that $\lvert A_i\rvert \geq \tfrac{2}{5}\sqrt{n}$ for all $i$ and $\lvert A_i\cap A_j\rvert\leq 1$ for all $i\neq j$, and yet if $B$ has non-empty intersection with all $A_i$ then there exists $A_j$ such that $\lvert B\cap A_j\rvert \gg \log n$. (The construction is to take random subsets of the lines of a projective plane.) The weaker version that Erdős posed in [Er81] remains open, although Alon conjectures the answer there to also be no. See [1159] for a weaker version, in which the family is the collection of lines of a finite projective plane. Additional thanks to : LouisD Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 27 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #664, https://www.erdosproblems.com/664, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable JoshuaB Working on formalising None Previous Next
-/


-- @category research open

import Mathlib
open Classical








open Classical Filter

namespace Erdos664

/-- `IsAdmissible c n m A` formalizes the hypotheses on a family of finite subsets.
The universe `{1, ..., n}` is represented by `Fin n`, and the family is indexed by
`Fin m`. -/
def IsAdmissible (c : ℝ) (n m : ℕ) (A : Fin m → Finset (Fin n)) : Prop :=
  (∀ i, c * Real.sqrt (n : ℝ) < (A i).card) ∧
    (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1)

/-- `HitsEveryWithBound A B K` says that `B` meets every member of `A` and that
each intersection has cardinality at most `K`. -/
def HitsEveryWithBound {n m : ℕ} (A : Fin m → Finset (Fin n))
    (B : Finset (Fin n)) (K : ℕ) : Prop :=
  ∀ i, B ∩ A i ≠ ∅ ∧ (B ∩ A i).card ≤ K

/-- The weaker Erdős question from the source: for every `c < 1`, there should
be a uniform finite bound depending only on `c`, valid for every admissible
family, with a hitting set realizing that bound. The notation `\ll_c 1` is
represented by the existentially quantified natural-number bound `K`.

The source asks for a set `B` meeting each `A_i` with bounded intersection;
this statement uses exactly that order of quantifiers. The resolution records
the stronger pairwise-balanced-design variant as settled negatively while
explicitly leaving this weaker version open. -/
def ErdosQuestion : Prop :=
  ∀ c : ℝ, c < 1 →
    ∃ K : ℕ, ∀ n m : ℕ, ∀ A : Fin m → Finset (Fin n),
      IsAdmissible c n m A → ∃ B : Finset (Fin n), HitsEveryWithBound A B K

/-- A proved sanity check: the one-member family consisting of the whole
one-point universe has a hitting set with bound one. This exercises the
formalized hitting-set predicate on a nonempty family. -/
theorem control_has_bounded_hitting_set :
    let A : Fin 1 → Finset (Fin 1) := fun _ => Finset.univ
    ∃ B : Finset (Fin 1), HitsEveryWithBound A B 1 := by
  dsimp
  refine ⟨Finset.univ, ?_⟩
  intro i
  simp [HitsEveryWithBound]

end Erdos664

#print axioms Erdos664.control_has_bounded_hitting_set
