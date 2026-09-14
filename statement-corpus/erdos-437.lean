/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $1\leq a_1<\cdots<a_k\leq x$. How many of the partial products $a_1,a_1a_2,\ldots,a_1\cdots a_k$ can be squares? Is it true that, for any $\epsilon>0$, there can be more than $x^{1-\epsilon}$ squares?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#437 : [ErGr80] number theory Erdős and Graham write it is 'trivial' that there are $o(x)$ many such squares, although this is not quite trivial, using Siegel's theorem. A positive answer follows from work of Bui, Pratt, and Zaharescu [BPZ24] , as noted by Tao in this blog post . In particular Tao shows that, if $L(x)$ is the maximal number of such squares possible, and $u(x)=(\log x\log\log x)^{1/2}$, then\[x\exp(-(2^{1/2}+o(1))u(x)) \leq L(x) \leq x\exp(-(2^{-1/2}+o(1))u(x)).\]See also [841] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #437, https://www.erdosproblems.com/437, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos437

/-- A natural number is a square when it is the product of a natural number
with itself. -/
def IsSquare (n : ℕ) : Prop :=
  ∃ y : ℕ, y * y = n

/-- `Admissible x k a` formalizes `1 ≤ a₁ < ⋯ < aₖ ≤ x`, for a sequence
indexed by `Fin k`. -/
def Admissible (x k : ℕ) (a : Fin k → ℕ) : Prop :=
  1 ≤ k ∧
    (∀ i, 1 ≤ a i ∧ a i ≤ x) ∧
    (∀ i j, i < j → a i < a j)

/-- The partial product ending at `i`; the product is taken over all indices
up to `i`, with the remaining factors replaced by `1`. -/
def partialProduct {k : ℕ} (a : Fin k → ℕ) (i : Fin k) : ℕ :=
  ∏ j : Fin k, if j ≤ i then a j else 1

/-- The number of square partial products in a finite increasing sequence. -/
noncomputable def squareCount {k : ℕ} (a : Fin k → ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => IsSquare (partialProduct a i))).card

/-- A direct formalization of the positive-answer part of the question:
for every positive real `ε`, arbitrarily large `x` admit an admissible
sequence whose number of square partial products exceeds `x^(1-ε)`.
The resolution records this as a settled result, while its analytic proof is
not reproduced here. -/
def PositiveAnswer : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ x : ℕ, N ≤ x ∧
      ∃ k : ℕ, ∃ a : Fin k → ℕ,
        Admissible x k a ∧
          (squareCount a : ℝ) > Real.rpow (x : ℝ) (1 - ε)

/-- Sanity control: the sole partial product of the one-term sequence `(1)`
is a square, so the square-count predicate is not identically empty. -/
theorem squareCount_singleton_one :
    0 < squareCount (fun _ : Fin 1 => 1) := by
  classical
  rw [squareCount]
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change IsSquare (partialProduct (fun _ : Fin 1 => 1) 0)
  rw [show partialProduct (fun _ : Fin 1 => 1) 0 = 1 by
    simp [partialProduct]]
  exact ⟨1, by simp⟩

/-- The positive answer recorded in the resolution. Its proof requires the
external analytic results cited in the source and remains an explicit,
honest proof gap in this formalization. -/
theorem positive_answer : PositiveAnswer := by
  sorry

#print axioms squareCount_singleton_one
#print axioms positive_answer

end Erdos437
