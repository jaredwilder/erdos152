import Mathlib


noncomputable section
open scoped BigOperators Topology
open Filter

def PrimeAP (N k : ℕ) : Prop :=
  ∃ a : Fin (N + 1), ∃ d : Fin (N + 1),
    1 ≤ a.1 ∧
    1 ≤ d.1 ∧
    ∀ i : Fin k,
      Nat.Prime (a.1 + i.1 * d.1) ∧
      1 ≤ a.1 + i.1 * d.1 ∧
      a.1 + i.1 * d.1 ≤ N

instance (N k : ℕ) : Decidable (PrimeAP N k) := by
  unfold PrimeAP
  infer_instance

def longestAP (N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (fun k => PrimeAP N k) |>.sup id

theorem witness_pos : PrimeAP 5 2 := by
  decide

theorem witness_neg : ¬ PrimeAP 5 3 := by
  decide

theorem erdosProblem200 :
    Tendsto
      (fun N : ℕ => (longestAP N : ℝ) / Real.log (N : ℝ))
      atTop
      (𝓝 0) := by
  sorry

end