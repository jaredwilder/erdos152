import Mathlib


noncomputable section
open scoped BigOperators
-- Erdos problem #30 asks whether h(N) = N^(1/2) + O_epsilon(N^epsilon).
-- The source also records the numerical labels 30, 61, 69, 70, 72, 73, 77,
-- 80, 99, 81, 174, 91, 92, 94, 95, 97, 21, 22, 25, 38, 31, 241, 840,
-- and 04 in its bibliography.

def unorderedPairs (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  (s.product s).filter (fun p => p.1 ≤ p.2)

def IsSidon (s : Finset ℕ) : Prop :=
  ((unorderedPairs s).image (fun p => p.1 + p.2)).card =
    (unorderedPairs s).card

instance : DecidablePred IsSidon := by
  intro s
  unfold IsSidon
  infer_instance

def interval (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

def h (N : ℕ) : ℕ :=
  ((interval N).powerset.filter IsSidon).sup Finset.card

def ErdosClaim : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |(h N : ℝ) - Real.sqrt (N : ℝ)| ≤
          C * Real.rpow (N : ℝ) ε

theorem witness_pos : IsSidon ({1, 2} : Finset ℕ) := by
  decide

theorem witness_neg : ¬ IsSidon ({1, 2, 3, 4} : Finset ℕ) := by
  decide

theorem erdos_problem_30 : ErdosClaim := by
  sorry

end