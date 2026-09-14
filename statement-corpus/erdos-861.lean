/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(N)$ be the size of the largest Sidon subset of $\{1,\ldots,N\}$ and $A(N)$ be the number of Sidon subsets of $\{1,\ldots,N\}$. Is it true that\[A(N)/2^{f(N)}\to \infty?\]Is it true that\[A(N) = 2^{(1+o(1))f(N)}?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#861 : [Er92c,p.38] number theory | sidon sets A problem of Cameron and Erdős. It is known that $f(N)\sim N^{1/2}$ and conjectured (see [30] ) that $f(N)=N^{1/2}+O(N^{\epsilon})$. While $A(N)$ has not been completely determined, both of these questions are now settled, the first positively and the second negatively. The current best bounds are (for large $N$)\[2^{1.16f(N)}\leq A(N) \leq 2^{6.442f(N)}.\]The lower bound is due to Saxton and Thomason [SaTh15] , the upper bound is due to Kohayakawa, Lee, Rödl, and Samotij [KLRS15] . See also [862] . This is discussed in problem C9 of Guy's collection [Gu04] . Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 15 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #861, https://www.erdosproblems.com/861, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A143824 , A227590 , A003022 , A143823 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next </h
-/


import Mathlib
open Filter
open Topology

-- @category research solved








open Classical Filter

namespace Erdos861

/-- A finite set is Sidon when distinct ordered pairs of increasing elements have distinct sums. -/
def IsSidon {N : ℕ} (s : Finset (Fin N)) : Prop :=
  ∀ a b c d : Fin N,
    a ∈ s → b ∈ s → c ∈ s → d ∈ s →
    a < b → c < d → a + b = c + d → a = c ∧ b = d

/-- POSITIVE WITNESS: `{0,1,3}` is a Sidon subset of `Fin 5`. -/
theorem isSidon_witness_pos :
    IsSidon ({0, 1, 3} : Finset (Fin 5)) := by
  decide

/-- NEGATIVE WITNESS: `{0,1,2,3}` is a near miss, failing only because `0+3 = 1+2`. -/
theorem isSidon_witness_neg :
    ¬ IsSidon ({0, 1, 2, 3} : Finset (Fin 5)) := by
  decide

/-- A Boolean, bounded and decidable version of the Sidon predicate on `Fin N`. -/
def IsSidonFinite (N : ℕ) (s : Finset (Fin N)) : Bool :=
  decide (IsSidon s)

/-- POSITIVE WITNESS: the Boolean finite Sidon test accepts `{0,1,3}`. -/
theorem isSidonFinite_witness_pos :
    IsSidonFinite 5 ({0, 1, 3} : Finset (Fin 5)) = true := by
  decide

/-- NEGATIVE WITNESS: the Boolean finite Sidon test rejects the near miss `{0,1,2,3}`. -/
theorem isSidonFinite_witness_neg :
    IsSidonFinite 5 ({0, 1, 2, 3} : Finset (Fin 5)) = false := by
  decide

/-- The Sidon subsets of `Fin N`, representing the subsets of `{1,...,N}` after translation. -/
def sidonSets (N : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Fin N)).powerset.filter IsSidon

/-- The empty set is always among the finite Sidon subsets. -/
theorem empty_mem_sidonSets (N : ℕ) :
    ∅ ∈ sidonSets N := by
  simp [sidonSets, IsSidon]

/-- The finite family of Sidon subsets is nonempty, so its cardinality is not a vacuous count. -/
theorem sidonSets_nonempty (N : ℕ) :
    (sidonSets N).Nonempty := by
  exact ⟨∅, empty_mem_sidonSets N⟩

/-- The finite analogue of `f(N)`, defined as the supremum of cardinalities inside a nonempty finite family. -/
def f (N : ℕ) : ℕ :=
  (sidonSets N).sup (fun s => s.card)

/-- The finite analogue of `A(N)`, namely the number of Sidon subsets of `Fin N`. -/
def A (N : ℕ) : ℕ :=
  (sidonSets N).card

/-- The count `A(N)` is positive because the empty Sidon set is present. -/
theorem A_pos (N : ℕ) :
    0 < A N := by
  apply Finset.card_pos.mpr
  exact sidonSets_nonempty N

/-- The first question, formalized as divergence of the ratio along the natural numbers. -/
def QuestionOne : Prop :=
  Tendsto
    (fun N : ℕ => (A N : ℝ) / ((2 : ℝ) ^ f N))
    atTop atTop

/-- The second question, formalized by the logarithmic equivalent of
`A(N) = 2^((1+o(1))f(N))`. -/
def QuestionTwo : Prop :=
  Tendsto
    (fun N : ℕ =>
      Real.log (A N : ℝ) / ((f N : ℝ) * Real.log 2))
    atTop (𝓝 1)

/-- The source records that the first question has a positive answer and the second has a negative answer.
The asymptotic formulation of the second question is represented by `QuestionTwo` above. -/
theorem resolution :
    QuestionOne ∧ ¬ QuestionTwo := by
  sorry Erdos861
