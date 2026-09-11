import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  The divisor-counting function τ and h(n) = n + τ(n).
  The recursive definition below represents h₁ = h and
  hₖ₊₁ = h ∘ hₖ.
-/
def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

def h (n : ℕ) : ℕ :=
  n + tau n

def hIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => hIter k (h n)

/-- Equality of two positive iterates, with both indices bounded by `B`. -/
def OrbitMeetWithin (B m n : ℕ) : Prop :=
  ∃ i : Fin (B + 1), ∃ j : Fin (B + 1),
    1 ≤ i.val ∧
    1 ≤ j.val ∧
    hIter i.val m = hIter j.val n

/-
  This is equivalent to the original assertion: any positive indices i and j
  are represented in Fin (B + 1) for a sufficiently large B.
  The positivity assumptions express that the original inputs are positive
  integers, as required for the divisor-counting formulation.
-/
def Erdos414 : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → ∃ B : ℕ, OrbitMeetWithin B m n

theorem witness_pos : OrbitMeetWithin 1 1 1 := by
  refine ⟨⟨1, by decide⟩, ⟨1, by decide⟩, by decide, by decide, rfl⟩

theorem witness_neg : ¬ OrbitMeetWithin 1 1 2 := by
  rintro ⟨i, j, hi, hj, hEq⟩
  have hi_lt : i.val < 2 := i.isLt
  have hj_lt : j.val < 2 := j.isLt
  have hi' : i.val = 1 := by omega
  have hj' : j.val = 1 := by omega
  have hEq' : hIter 1 1 = hIter 1 2 := by
    simpa [hi', hj'] using hEq
  have hne : hIter 1 1 ≠ hIter 1 2 := by decide
  exact hne hEq'

theorem erdos_414 : Erdos414 := by
  sorry

end