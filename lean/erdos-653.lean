import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-- A point of the plane, represented by its two real coordinates. -/
abbrev Point := Fin 2 → ℝ

/-- Squared Euclidean distance.  Equality of squared distances is equivalent
to equality of the corresponding nonnegative Euclidean distances. -/
noncomputable def squaredDistance (p q : Point) : ℝ :=
  ∑ d : Fin 2, (p d - q d) ^ 2

/-- The number of distinct distances from a point to the other points. -/
noncomputable def radius (p : Fin n → Point) (i : Fin n) : ℕ :=
  ((Finset.univ.filter (fun j : Fin n => j ≠ i)).image
    (fun j => squaredDistance (p j) (p i))).card

/-- The number of distinct values among all the radii of a configuration. -/
noncomputable def distinctRadiusCount (p : Fin n → Point) : ℕ :=
  (Finset.univ.image (fun i => radius p i)).card

/-- The maximum possible number of distinct radius values for n points. -/
noncomputable def g (n : ℕ) : ℕ :=
  Nat.findGreatest
    (fun k => ∃ p : Fin n → Point, distinctRadiusCount p = k) n

/-- The finite-instance predicate used for the witness checks. -/
def hasAtLeast (p : Fin n → Point) (k : ℕ) : Prop :=
  k ≤ distinctRadiusCount p

theorem witness_pos :
    hasAtLeast (fun _ : Fin 1 => (0 : Point)) 1 := by
  classical
  simp [hasAtLeast, distinctRadiusCount, radius, squaredDistance]

theorem witness_neg :
    ¬ hasAtLeast (fun _ : Fin 1 => (0 : Point)) 2 := by
  classical
  simp [hasAtLeast, distinctRadiusCount, radius, squaredDistance]

/-- The constants appearing in the known lower bounds for this problem. -/
def erdosFishburnConstant : ℝ := 3 / 8

def csizmadiaConstant : ℝ := 7 / 10

def gapExponent : ℝ := 2 / 3

/-- A formal version of the assertion that g(n) ≥ (1-o(1)) n. -/
def asymptoticLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - ε) * (n : ℝ) ≤ (g n : ℝ)

/-- Erdős problem 653. -/
theorem erdos_653 : asymptoticLowerBound := by
  sorry

end
