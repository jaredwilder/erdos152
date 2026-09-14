/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subset\mathbb{N}$ be an additive basis of order $k$. Let $B=\{b_1<b_2<\cdots\}$ be the set of integers which are the sum of $k$ or fewer distinct $a\in A$. Is it true that $b_{n+1}-b_n=O(1)$? (Where the implied constant may depend on both $A$ and $k.)

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#880 : [Er98] number theory | additive basis A problem of Burr and Erdős. Hegyvári, Hennecart, and Plagne [HHP07] showed the answer is yes for $k=2$ (in fact with $b_{n+1}-b_n\leq 2$ for large $n$) but no for $k\geq 3$. The proof that $b_{n+1}-b_n\leq 2$ for $k=2$ is trivial, since clearly all odd numbers in $A+A$ must be the sum of two distinct elements from $A$. Additional thanks to : Euro Sampaio Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #880, https://www.erdosproblems.com/880, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable JoshuaB Working on formalising gotrevor Previous Next
-/




import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos880

/-- A finite bounded version of representing every number below `N` as a sum of at
most `k` distinct elements of `A`. -/
def RepresentsUpTo (A : Finset (Fin M)) (k N : ℕ) : Prop :=
  ∀ n : Fin N, ∃ s : Finset (Fin M),
    s ⊆ A ∧ s.card ≤ k ∧ s.sum (fun x => x.val) = n.val

/-- POSITIVE WITNESS: the full finite interval represents every number below `4`
using at most two distinct elements. -/
theorem RepresentsUpTo_witness_pos :
    RepresentsUpTo (M := 6) (Finset.univ : Finset (Fin 6)) 2 4 := by
  decide

/-- NEGATIVE WITNESS: removing the element `2` from the full interval prevents
representation of `3` with at most two distinct elements. -/
theorem RepresentsUpTo_witness_neg :
    ¬ RepresentsUpTo (M := 6) ({0, 1} : Finset (Fin 6)) 2 4 := by
  decide

/-- The finite set of sums of at most `k` distinct elements of `A` whose value
lies in the finite interval `Fin M`. -/
def IsRepresented (A : Finset (Fin M)) (k : ℕ) (y : Fin M) : Prop :=
  ∃ s : Finset (Fin M),
    s ⊆ A ∧ s.card ≤ k ∧ s.sum (fun x => x.val) = y.val

/-- POSITIVE WITNESS: `3` is represented by `0+1+2` with at most three
distinct elements of the indicated finite set. -/
theorem IsRepresented_witness_pos :
    IsRepresented (M := 6) ({0, 1, 2} : Finset (Fin 6)) 3 3 := by
  decide

/-- NEGATIVE WITNESS: `4` is not represented using at most two distinct
elements of `{0,1,2}`. -/
theorem IsRepresented_witness_neg :
    ¬ IsRepresented (M := 6) ({0, 1, 2} : Finset (Fin 6)) 2 4 := by
  decide

/-- A bounded finite analogue of bounded gaps: every point of the interval
`Fin M` lies within `c` above some represented sum. -/
def HasFiniteGapBound (A : Finset (Fin M)) (k c : ℕ) : Prop :=
  ∀ x : Fin M, ∃ y : Fin M,
    IsRepresented A k y ∧ x.val ≤ y.val ∧ y.val ≤ x.val + c

/-- POSITIVE WITNESS: the full interval has represented sums with gap bound
one when sums of at most two distinct elements are allowed. -/
theorem HasFiniteGapBound_witness_pos :
    HasFiniteGapBound (M := 6) (Finset.univ : Finset (Fin 6)) 2 1 := by
  decide

/-- NEGATIVE WITNESS: although `{0,1,2}` represents every number below `4`
with at most two distinct summands, its represented sums do not have gap
bound one throughout `Fin 6`. -/
theorem HasFiniteGapBound_witness_neg :
    ¬ HasFiniteGapBound (M := 6) ({0, 1, 2} : Finset (Fin 6)) 2 1 := by
  decide

/-- A decidable finite-instance formalization of the source question.

The source asks whether the set of sums of at most `k` distinct elements has
bounded successive gaps.  Here `RepresentsUpTo A k N` is the bounded additive
basis hypothesis, while `HasFiniteGapBound A k c` tests bounded gaps on the
finite interval `Fin M`.  This finite predicate is a computable proxy and is
not asserted to be equivalent to the asymptotic statement in the source. -/
def QuestionFinite (A : Finset (Fin M)) (k N c : ℕ) : Prop :=
  RepresentsUpTo A k N → HasFiniteGapBound A k c

/-- POSITIVE WITNESS: the finite full-interval instance satisfies the bounded
finite version of the question. -/
theorem QuestionFinite_witness_pos :
    QuestionFinite (M := 6) (Finset.univ : Finset (Fin 6)) 2 4 1 := by
  decide

/-- NEGATIVE WITNESS: `{0,1,2}` is a near miss: it represents all numbers below
`4`, but its represented sums fail the proposed gap bound on `Fin 6`. -/
theorem QuestionFinite_witness_neg :
    ¬ QuestionFinite (M := 6) ({0, 1, 2} : Finset (Fin 6)) 2 4 1 := by
  decide

end Erdos880
