import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

abbrev Point := ℚ × ℚ

def sqDist (p q : Point) : ℚ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def distanceCount (A : Finset Point) (x : Point) : ℕ :=
  (A.image (sqDist x)).card

def HasPinnedDistances (A : Finset Point) (k : ℕ) : Prop :=
  ∃ x ∈ A, k ≤ distanceCount A x

/-- The `n^(1-o(1))` formulation of the pinned distance question. -/
def WeakPinnedDistanceConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ A : Finset Point, N ≤ A.card →
      ∃ x ∈ A,
        (A.card : ℝ) ^ (1 - ε) ≤ (distanceCount A x : ℝ)

/-- The stronger `n / sqrt(log n)` formulation of the pinned distance question. -/
def StrongPinnedDistanceConjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ N : ℕ, ∀ A : Finset Point, N ≤ A.card →
      ∃ x ∈ A,
        c * (A.card : ℝ) / Real.sqrt (Real.log (A.card : ℝ))
          ≤ (distanceCount A x : ℝ)

/-- The question asks whether the first assertion, or even the stronger one, holds. -/
def PinnedDistanceQuestion : Prop :=
  WeakPinnedDistanceConjecture ∨ StrongPinnedDistanceConjecture

theorem witness_pos :
    HasPinnedDistances ({(0, 0), (1, 0)} : Finset Point) 2 := by
  refine ⟨(0, 0), by simp, ?_⟩
  norm_num [distanceCount, sqDist]

theorem witness_neg :
    ¬ HasPinnedDistances ({(0, 0), (1, 0)} : Finset Point) 3 := by
  intro h
  rcases h with ⟨x, hx, hcount⟩
  have hc : distanceCount ({(0, 0), (1, 0)} : Finset Point) x ≤ 2 := by
    unfold distanceCount
    calc
      (({(0, 0), (1, 0)} : Finset Point).image (sqDist x)).card
          ≤ ({(0, 0), (1, 0)} : Finset Point).card := Finset.card_image_le
      _ = 2 := by norm_num
  omega

/-- Numeric data appearing in the accompanying source entry. -/
def sourceNumerals : Finset ℕ :=
  {0, 1, 2, 14, 16, 48, 55, 89, 97, 500}

/-- The decimal approximation recorded for the exponent in the source entry. -/
def sourceExponentApproximation : ℝ :=
  0.864137

theorem pinned_distance_question : PinnedDistanceQuestion := by
  sorry

end