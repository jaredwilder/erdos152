/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subseteq \mathbb{N}$ be a set with positive upper density. Must there exist an infinite set $B\subseteq A$ and integer $t$ such that\[\{b_1+b_2: b_1\neq b_2\in B\}+t\subseteq A?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#656 : [Er75b] [Er80,p.105] number theory | additive combinatorics Erdős [Er75b] posed this as a candidate for a density version of Hindman's theorem (see [172] ). This is true, and was proved by Kra, Moreira, Richter, and Robertson [KMRR24] . See also [109] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 07 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #656, https://www.erdosproblems.com/656, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos656

/-- The number of elements of `A` below `N`, used to express upper density. -/
def upperCount (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range N).filter (fun n => n ∈ A) |>.card

/-- A set has positive upper density when some positive real density is
attained along arbitrarily large initial intervals. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ M : ℕ, ∃ N : ℕ,
      M ≤ N ∧ 0 < N ∧
        δ ≤ ((upperCount A N : ℕ) : ℝ) / (N : ℝ)

/-- `ShiftedPairSumsIn A B t` means that every sum of two distinct elements
of `B`, shifted by the integer `t`, belongs to `A`. The integer is represented
by requiring equality with the cast of an element of `A`. -/
def ShiftedPairSumsIn (A B : Set ℕ) (t : ℤ) : Prop :=
  ∀ ⦃b₁ b₂ : ℕ⦄,
    b₁ ∈ B → b₂ ∈ B → b₁ ≠ b₂ →
      ∃ a ∈ A, (b₁ : ℤ) + (b₂ : ℤ) + t = (a : ℤ)

/-- The formal statement of Erdős problem 656. -/
def ErdosQuestion : Prop :=
  ∀ A : Set ℕ,
    HasPositiveUpperDensity A →
      ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ t : ℤ, ShiftedPairSumsIn A B t

/-- The resolved assertion recorded for Erdős problem 656, proved in the
literature by Kra, Moreira, Richter, and Robertson. The proof is not
reproduced here; the remaining gap is the imported additive-combinatorial
theorem. -/
theorem erdos656_resolution :
    ∀ A : Set ℕ,
      HasPositiveUpperDensity A →
        ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∃ t : ℤ, ShiftedPairSumsIn A B t := by
  sorry

/-- The named resolution theorem implies the proposition packaging the
original question. This derivation is kernel-checked; its input is the
sorried literature result above. -/
theorem erdos656_answers_question : ErdosQuestion := by
  intro A hA
  exact erdos656_resolution A hA

/-- Control computation: the whole set of natural numbers has positive upper
density according to the definition. The density witness is `1 / 2`; the
chosen interval is always `M + 1`, so the denominator is nonzero. -/
theorem univ_has_positive_upper_density :
    HasPositiveUpperDensity (Set.univ : Set ℕ) := by
  refine ⟨(1 : ℝ) / 2, by norm_num, ?_⟩
  intro M
  refine ⟨M + 1, Nat.le_succ M, Nat.succ_pos M, ?_⟩
  have hpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by
    positivity
  have hquot :
      ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) = 1 :=
    div_self (ne_of_gt hpos)
  have hbound :
      (1 : ℝ) / 2 ≤ ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) := by
    rw [hquot]
    norm_num
  simpa [upperCount] using hbound

/-- Control example: the conclusion is nonvacuously satisfiable for the
whole set, with `B = ℕ` and shift `t = 0`. -/
theorem univ_satisfies_conclusion :
    ∃ B : Set ℕ, B.Infinite ∧ B ⊆ (Set.univ : Set ℕ) ∧
      ∃ t : ℤ, ShiftedPairSumsIn (Set.univ : Set ℕ) B t := by
  refine ⟨Set.univ, Set.infinite_univ, Set.subset_univ, 0, ?_⟩
  intro b₁ b₂ _ _ _
  refine ⟨b₁ + b₂, by simp, ?_⟩
  simp

#print axioms univ_has_positive_upper_density
#print axioms univ_satisfies_conclusion

end Erdos656
