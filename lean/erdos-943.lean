import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def erdosProblemNumber : ℕ := 943

def Powerful (n : ℕ) : Prop :=
  0 < n ∧
    ∀ p ∈ Finset.range (n + 1),
      Nat.Prime p → p ∣ n → p ^ 2 ∣ n

instance powerfulDecidable (n : ℕ) : Decidable (Powerful n) := by
  unfold Powerful
  infer_instance

def convolution (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun d => d ∣ n ∧ Powerful d ∧ Powerful (n / d))).card

def Subpolynomial (f : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ C N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → f n ^ k ≤ C * n

theorem witness_pos : Powerful 1 := by
  decide

theorem witness_neg : ¬ Powerful 2 := by
  decide

theorem erdos_943 : Subpolynomial convolution := by
  sorry

end
