import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem 385.

Let F(n) = max over composite m < n of m + p(m), where p(m) is
the least prime divisor of m.  The source asks whether F(n) > n for
all sufficiently large n, and whether F(n) - n tends to infinity.

The resolution records #385, references [Er79d,p.73], [ErGr80,p.74],
[430], and [463], and mentions the possible bound
n + (1-o(1)) * sqrt n, together with the trivial upper bound
n + sqrt n.  The database citation is accessed 2026-08-30 and lists
OEIS A322292.
-/

def isComposite (m : ℕ) : Prop :=
  1 < m ∧ ¬ Nat.Prime m

def p (m : ℕ) : ℕ :=
  Nat.minFac m

/-- The maximum is taken to be 0 when the indexing set is empty. -/
def F : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      max (F n) (if isComposite n then n + p n else 0)

def Above (n : ℕ) : Prop :=
  F n > n

def EventuallyAbove : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, Above n

def Diverges : Prop :=
  Filter.Tendsto (fun n : ℕ => F n - n) Filter.atTop Filter.atTop

def Erdos385 : Prop :=
  EventuallyAbove ∧ Diverges

theorem witness_pos : Above 5 := by
  norm_num [Above, F, isComposite, p]

theorem witness_neg : ¬ Above 3 := by
  norm_num [Above, F, isComposite, p]

theorem erdos_385 : Erdos385 := by
  sorry

end