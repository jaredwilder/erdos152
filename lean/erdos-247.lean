import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
The positive integers in the source are represented by `ℕ`; the lower bound
`1 ≤ a 0` ensures that this is equivalent to an integer-valued sequence.
The source indexing starts at `a₁`, so `a 0` represents `a₁`.
-/

def StrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, a n < a (n + 1)

def RatioLimsupInfinite (a : ℕ → ℕ) : Prop :=
  ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ C < (a (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)

def Erdos247Admissible (a : ℕ → ℕ) : Prop :=
  1 ≤ a 0 ∧ StrictlyIncreasing a ∧ RatioLimsupInfinite a

def Erdos247 : Prop :=
  ∀ a : ℕ → ℕ,
    Erdos247Admissible a →
      Transcendental ℚ
        (∑' n : ℕ, (1 : ℝ) / (2 : ℝ) ^ a (n + 1))

/-
A small decidable finite-prefix predicate is included to give concrete
positive and negative kernel-checkable witnesses.
-/
def FiniteAdmissible (s : Fin 3 → ℕ) : Prop :=
  1 ≤ s 0 ∧ ∀ i j : Fin 3, i.val < j.val → s i < s j

def positivePrefix : Fin 3 → ℕ :=
  fun i =>
    if i = (0 : Fin 3) then 1
    else if i = (1 : Fin 3) then 2
    else 3

def negativePrefix : Fin 3 → ℕ :=
  fun i =>
    if i = (0 : Fin 3) then 1
    else if i = (1 : Fin 3) then 1
    else 3

theorem witness_pos : FiniteAdmissible positivePrefix := by
  unfold FiniteAdmissible
  constructor
  · norm_num [positivePrefix]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [positivePrefix] at hij <;>
      norm_num [positivePrefix]

theorem witness_neg : ¬ FiniteAdmissible negativePrefix := by
  intro h
  have hlt :=
    h.2 (0 : Fin 3) (1 : Fin 3) (by norm_num)
  norm_num [negativePrefix] at hlt

theorem erdos_problem_247 : Erdos247 := by
  sorry

end