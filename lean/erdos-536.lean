import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem #536.

The source asks for the largest subset of `{1, ..., N}` having no three
distinct elements with equal pairwise least common multiples, and asks whether
this largest size is `o(N)`.

Source literals: 536, 64, 646, 70, 124, 73, 1991, 62, 67, 1, 0, 221, 225,
535, 537, 856, 857, 2026, 8, 30, 10, 3, 4.
-/

/-- A finite set is admissible for the problem at scale `N`. -/
def Good (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      a ≠ b →
      a ≠ c →
      b ≠ c →
      ¬ (Nat.lcm a b = Nat.lcm b c ∧ Nat.lcm a b = Nat.lcm a c)

/-- The largest cardinality of an admissible subset of `{1, ..., N}`. -/
def f (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).powerset.sup (fun A =>
    if Good N A then A.card else 0)

/-- The epsilon formulation of the assertion that `f(N) = o(N)`. -/
def IsSmall : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (f N : ℝ) ≤ ε * (N : ℝ)

/-- Three elements can be admissible when their pairwise lcms are unequal. -/
theorem witness_pos : Good 3 {1, 2, 3} := by
  norm_num [Good, Finset.subset_iff, Nat.lcm]

/-- The triple `{2, 3, 6}` has the common pairwise lcm `6`, so it is not admissible. -/
theorem witness_neg : ¬ Good 6 {2, 3, 6} := by
  intro h
  have h' := h.2 2 (by simp) 3 (by simp) 6 (by simp)
    (by norm_num) (by norm_num) (by norm_num)
  exact h' (by norm_num [Nat.lcm])

/-- The open question from Erdős problem #536. -/
theorem f_is_o : IsSmall := by
  sorry

end