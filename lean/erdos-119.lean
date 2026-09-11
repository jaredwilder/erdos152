import Mathlib

open scoped BigOperators

noncomputable section

def polynomial (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.Icc 1 n, (z - a i)

def unitSequence (a : ℕ → ℂ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → ‖a i‖ = 1

def maximumModulus (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖polynomial a n z‖}

def limsupInfinite (a : ℕ → ℂ) : Prop :=
  ∀ B : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ B < maximumModulus a n

def infinitelyOftenPower (a : ℕ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ (n : ℝ) ^ c < maximumModulus a n

def summedPowerGrowth (a : ℕ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (∑ k ∈ Finset.Icc 1 n, maximumModulus a k) > (n : ℝ) ^ (1 + c)

def erdosProblem119 : Prop :=
  ∀ a : ℕ → ℂ, unitSequence a →
    limsupInfinite a ∧ infinitelyOftenPower a ∧ summedPowerGrowth a

/-- A decidable finite analogue of the power-growth question. -/
def finitePowerGrowth {n : ℕ} (m : Fin n → ℕ) : Prop :=
  ∃ c : Fin n, 0 < c.val ∧
    ∀ k : Fin n, c.val ≤ k.val →
      k.val ^ (1 + c.val) < m k

theorem witness_pos :
    finitePowerGrowth (fun _ : Fin 2 => 2) := by
  refine ⟨⟨1, by decide⟩, by decide, ?_⟩
  intro k hk
  fin_cases k
  · norm_num at hk
  · norm_num

theorem witness_neg :
    ¬ finitePowerGrowth (fun _ : Fin 2 => 0) := by
  intro h
  rcases h with ⟨c, hc, hgrowth⟩
  fin_cases c
  · norm_num at hc
  · have h := hgrowth ⟨1, by decide⟩ (by decide)
    norm_num at h

theorem erdos_problem_119 : erdosProblem119 := by
  sorry