import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  We use rational coordinates, viewed inside ℝ², so that finite point
  configurations have a decidable underlying shape.  The distance is the
  ordinary Euclidean distance.
-/

abbrev Point := ℚ × ℚ

def euclideanDistance (p q : Point) : ℝ :=
  Real.sqrt (((p.1 : ℝ) - q.1) ^ 2 + ((p.2 : ℝ) - q.2) ^ 2)

def Admissible (P : Finset Point) : Prop :=
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    1 ≤ euclideanDistance p q) ∧
  (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, ∀ s ∈ P,
    euclideanDistance p q ≠ euclideanDistance r s →
      1 ≤ |euclideanDistance p q - euclideanDistance r s|)

def diameter (P : Finset Point) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ P, ∃ q ∈ P, x = euclideanDistance p q}

/-- The question asks whether the diameter is bounded below by a
positive constant times the number of points, for all sufficiently large
finite configurations satisfying the hypotheses. -/
def LinearDiameterClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ P : Finset Point, P.card = n → Admissible P →
        c * (n : ℝ) ≤ diameter P

/-- Numerical data appearing in the source entry. -/
def sourceReferenceNumbers : Finset ℕ :=
  {0, 3, 4, 5, 8, 9, 15, 30, 89, 90, 92, 95, 97, 100, 2026}

/-
  The source also mentions the values 1, 2, n - 1, n^(3/4), and n/log n;
  the constants 3 and 4 above record the exponent 3/4.
-/

theorem witness_pos :
    Admissible
      ({(0, 0), (1, 0)} : Finset Point) := by
  norm_num [Admissible, euclideanDistance]

theorem witness_neg :
    ¬ Admissible
      ({(0, 0), ((1 : ℚ) / 2, 0)} : Finset Point) := by
  norm_num [Admissible, euclideanDistance]

theorem erdos_problem_100 : LinearDiameterClaim := by
  sorry

end
