import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def problemNumber : ℕ := 89

def sourceNumericData : List ℕ :=
  [89, 46, 57, 61, 75, 99, 4, 69, 81, 82, 83, 85, 87, 170, 90, 92,
   95, 97, 15, 604, 1083, 0, 2026, 23, 1, 8, 30, 186704, 131628]

abbrev Point := ℚ × ℚ

def squaredDistance (p q : Point) : ℚ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def distanceCount (A : Finset Point) : ℕ :=
  (((A.product A).filter (fun p => p.1 ≠ p.2)).image
    (fun p => squaredDistance p.1 p.2)).card

def finiteDistanceClaim {m : ℕ} (points : Fin m → Point) (n k : ℕ) : Prop :=
  ∀ A : Finset (Fin m), A.card = n →
    k ≤ distanceCount (A.image points)

theorem witness_pos :
    finiteDistanceClaim (fun _ : Fin 1 => ((0, 0) : Point)) 1 0 := by
  intro A hA
  exact Nat.zero_le _

theorem witness_neg :
    ¬ finiteDistanceClaim
      (fun i : Fin 2 => if i = 0 then ((0, 0) : Point) else ((1, 0) : Point))
      2 2 := by
  intro h
  have hn :
      ¬ (2 ≤ distanceCount
        (({0, 1} : Finset (Fin 2)).image
          (fun i => if i = 0 then ((0, 0) : Point) else ((1, 0) : Point)))) := by
    native_decide
  exact hn (h ({0, 1} : Finset (Fin 2)) (by norm_num))

noncomputable def realDistanceCount (A : Finset (ℝ × ℝ)) : ℕ := by
  classical
  exact
    (((A.product A).filter (fun p => p.1 ≠ p.2)).image
      (fun p =>
        (p.1.1 - p.2.1) ^ 2 + (p.1.2 - p.2.2) ^ 2)).card

theorem erdos_problem_89 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset (ℝ × ℝ), A.card = n →
        c * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤
          (realDistanceCount A : ℝ) := by
  sorry

end