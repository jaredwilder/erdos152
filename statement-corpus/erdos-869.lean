/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $A_1,A_2$ are disjoint additive bases of order $2$ (i.e. $A_i+A_i$ contains all large integers) then must $A=A_1\cup A_2$ contain a minimal additive basis of order $2$ (one such that deleting any element creates infinitely many $n\not\in A+A$)?
-/

 /-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#869 : [ErNa88] [Er92c,p.44] number theory | additive basis A question of Erdős and Nathanson [ErNa88] . Härtter [Ha56] and Nathanson [Na74] proved that there exist additive bases which do not contain any minimal additive bases. Larsen has given a negative answer to this question; indeed, the three potential measures of 'robustness' of an additive basis, $1_A\ast 1_A(n)\to \infty$ as $n\to \infty$, $A$ is the union of two disjoint bases, and $A$ contains a minimal basis, are independent, in that Larsen constructs examples of bases satisfying any combination of these three properties (see [868] and [871] for other problems about the implication between these properties). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 02 May 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #869, https://www.erdosproblems.com/869, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical
open Filter








open Classical Filter

namespace Erdos869

/-- An additive basis of order two is a set whose pairwise sumset contains every
sufficiently large natural number. -/
def AdditiveBasis2 (A : Set ℕ) : Prop :=
  ∀ᶠ n in atTop, n ∈ A + A

/-- A minimal additive basis of order two is an additive basis for which deleting
any element leaves infinitely many natural numbers outside the resulting sumset. -/
def MinimalAdditiveBasis2 (A : Set ℕ) : Prop :=
  AdditiveBasis2 A ∧
    ∀ a ∈ A, Set.Infinite {n : ℕ | n ∉ (A \ ({a} : Set ℕ)) + (A \ ({a} : Set ℕ))}

/-- The question asks whether every union of two disjoint additive bases of order
two contains a minimal additive basis of order two. -/
def OriginalQuestion : Prop :=
  ∀ A₁ A₂ : Set ℕ,
    Disjoint A₁ A₂ →
    AdditiveBasis2 A₁ →
    AdditiveBasis2 A₂ →
    ∃ B : Set ℕ, B ⊆ A₁ ∪ A₂ ∧ MinimalAdditiveBasis2 B

/-- A bounded, decidable finite analogue of being an additive basis of order two:
every target in the first `n` natural numbers is a sum of two elements of `A`. -/
def AdditiveBasis2Finite (A : Finset ℕ) (n : ℕ) : Bool :=
  (Finset.range n).all (fun m =>
    (Finset.product A A).any (fun p => p.1 + p.2 = m))

/-- A bounded, decidable finite analogue of minimality: `A` covers the first
`n` targets, while deleting each element destroys that bounded coverage. -/
def MinimalAdditiveBasis2Finite (A : Finset ℕ) (n : ℕ) : Bool :=
  AdditiveBasis2Finite A n &&
    A.all (fun a => !(AdditiveBasis2Finite (A.erase a) n))

/-- POSITIVE WITNESS: `{0,1}` covers the first two targets, and deleting either
element destroys that property. -/
theorem MinimalAdditiveBasis2Finite_witness_pos :
    MinimalAdditiveBasis2Finite ({0, 1} : Finset ℕ) 2 = true := by
  decide

/-- NEGATIVE WITNESS: deleting `1` from the positive witness leaves `{0}`, which
fails exactly the target `1` in the bounded basis condition. -/
theorem MinimalAdditiveBasis2Finite_witness_neg :
    MinimalAdditiveBasis2Finite ({0} : Finset ℕ) 2 = false := by
  decide

/-- POSITIVE WITNESS: `{0,1}` represents both `0` and `1` as sums of two elements. -/
theorem AdditiveBasis2Finite_witness_pos :
    AdditiveBasis2Finite ({0, 1} : Finset ℕ) 2 = true := by
  decide

/-- NEGATIVE WITNESS: removing `1` leaves `{0}`, which misses the single target
`1` among the first two targets. -/
theorem AdditiveBasis2Finite_witness_neg :
    AdditiveBasis2Finite ({0} : Finset ℕ) 2 = false := by
  decide

/-- Larsen's negative resolution of the Erdős--Nathanson question: there are two
disjoint additive bases whose union contains no minimal additive basis of order
two. This declaration records the literature result; its proof remains to be
formalized. -/
theorem larsen_negative_answer :
    ∃ A₁ A₂ : Set ℕ,
      Disjoint A₁ A₂ ∧
      AdditiveBasis2 A₁ ∧
      AdditiveBasis2 A₂ ∧
      ¬ ∃ B : Set ℕ, B ⊆ A₁ ∪ A₂ ∧ MinimalAdditiveBasis2 B := by
  sorry

/-- The source asks whether every such union contains a minimal basis. The
recorded resolution is negative, so this is the negation of `OriginalQuestion`.
The source clause maps directly to disjoint `A₁,A₂`, additive-basis hypotheses,
and a minimal basis contained in their union. -/
theorem not_original_question : ¬ OriginalQuestion := by
  sorry

#print axioms MinimalAdditiveBasis2Finite_witness_pos
#print axioms MinimalAdditiveBasis2Finite_witness_neg
#print axioms AdditiveBasis2Finite_witness_pos
#print axioms AdditiveBasis2Finite_witness_neg

end Erdos869
