import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  A finite configuration of points in the Euclidean plane.  The predicate
  below says that a finite set of indices contains no pair at unit distance.
-/

abbrev Point := ℝ × ℝ

def unitDistance (p q : Point) : Prop :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 = 1

def NoUnitPair {n : ℕ} (p : Fin n → Point) (S : Finset (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ∈ S → j ∈ S → i ≠ j → ¬ unitDistance (p i) (p j)

/-- Every configuration of `n` points contains an independent set of
cardinality at least `q`. -/
def fAtLeast (n : ℕ) (q : ℚ) : Prop :=
  ∀ p : Fin n → Point,
    ∃ S : Finset (Fin n),
      NoUnitPair p S ∧ (S.card : ℚ) ≥ q

/-- The question asked in the problem, in its proposed quarter-density form. -/
def quarterBound : Prop :=
  ∀ n : ℕ, fAtLeast n ((n : ℚ) / 4)

/-
  Small computational witnesses for the predicate `NoUnitPair`.
-/

def pTwo : Fin 2 → Point :=
  ![(0, 0), (1, 0)]

def sOne : Finset (Fin 2) :=
  {0}

def sTwo : Finset (Fin 2) :=
  {0, 1}

theorem witness_pos : NoUnitPair pTwo sOne := by
  intro i j hi hj hne
  have hi0 : i = 0 := by simpa [sOne] using hi
  have hj0 : j = 0 := by simpa [sOne] using hj
  exact (hne (hi0.trans hj0.symm)).elim

theorem witness_neg : ¬ NoUnitPair pTwo sTwo := by
  intro h
  have hbad :=
    h (i := (0 : Fin 2)) (j := (1 : Fin 2))
      (by simp [sTwo]) (by simp [sTwo]) (by decide)
  norm_num [pTwo, unitDistance] at hbad

/-
  Numerical quantities occurring in the source discussion.
-/

def problemNumber : ℕ := 1070
def sourceYear : ℕ := 87
def sourcePage : ℕ := 171
def relatedProblem : ℕ := 508
def moserUpper : ℚ := 2 / 7
def moserApprox : ℚ := 0.285
def croftLower : ℚ := 0.22936
def quarter : ℚ := 1 / 4
def densityUpper : ℚ := 0.247
def densityProblem : ℕ := 232
def strictDistanceProblem : ℕ := 1066
def larmanRogersYear : ℕ := 72
def croftYear : ℕ := 67
def modernResultsYear : ℕ := 23
def revisionYear : ℕ := 2026
def revisionMonth : ℕ := 1
def revisionDay : ℕ := 22
def commentCount : ℕ := 8
def accessYear : ℕ := 2026
def accessMonth : ℕ := 8
def accessDay : ℕ := 30

/-- The proposed lower bound `f(n) ≥ n/4`; this is the open conjectural claim. -/
theorem quarter_bound_conjecture : quarterBound := by
  sorry

end