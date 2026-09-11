import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
A decidable rational-coordinate finite model of the Euclidean question.
The known bounds are `n^3 log n ≪ f(n) ≪ n^(7/2)`.
-/

def distSq (p q : ℚ × ℚ) : ℚ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def equalDistancePairs (ab cd : (ℚ × ℚ) × (ℚ × ℚ)) : Prop :=
  ab.1 ≠ ab.2 ∧
    cd.1 ≠ cd.2 ∧
    (ab.1 ≠ cd.1 ∨ ab.2 ≠ cd.2) ∧
    (ab.1 ≠ cd.2 ∨ ab.2 ≠ cd.1) ∧
    distSq ab.1 ab.2 = distSq cd.1 cd.2

def Degenerate (s : Finset (ℚ × ℚ)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, equalDistancePairs (a, b) (c, d)

def badCount (P : Finset (ℚ × ℚ)) : ℕ :=
  (P.powerset.filter (fun s => s.card = 4 ∧ Degenerate s)).card

def NearCubic : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ P : Finset (ℚ × ℚ), P.card = n →
          (badCount P : ℝ) ≤ C * Real.rpow (n : ℝ) (3 + ε)

def Ppos : Finset (ℚ × ℚ) :=
  {(0, 0), (1, 0), (0, 1), (1, 1)}

def Pneg : Finset (ℚ × ℚ) :=
  {(0, 0), (1, 0), (0, 2), (3, 3)}

theorem witness_pos : Degenerate Ppos := by
  norm_num [Degenerate, Ppos, equalDistancePairs, distSq]

theorem witness_neg : ¬ Degenerate Pneg := by
  norm_num [Degenerate, Pneg, equalDistancePairs, distSq]

theorem open_conjecture : NearCubic := by
  sorry

end