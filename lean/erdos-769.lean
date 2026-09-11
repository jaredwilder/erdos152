import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Erdős problem 769.

Let c(n) be minimal such that, whenever k ≥ c(n), the n-dimensional
unit cube can be decomposed into k homothetic n-dimensional cubes.

The numerical quantities appearing in the source include:
2, 6, 3, 48, 2^n + 2^(n-1), n^(n+1), 6^n, (2n)^(n-1),
2^(n+1)-1, 1.8 n^(n+1), e^2 n^n, 74, 98, 18, 2025, and 2026.
-/

def Point (n : ℕ) := Fin n → ℝ

def inCube (n : ℕ) (center : Point n) (side : ℝ) (x : Point n) : Prop :=
  ∀ i, |x i - center i| ≤ side / 2

def inInterior (n : ℕ) (center : Point n) (side : ℝ) (x : Point n) : Prop :=
  ∀ i, |x i - center i| < side / 2

def inUnitCube (n : ℕ) (x : Point n) : Prop :=
  inCube n (fun _ => (1 : ℝ) / 2) 1 x

def Decomposes (n k : ℕ) : Prop :=
  ∃ centers : Fin k → Point n, ∃ sides : Fin k → ℝ,
    (∀ j, 0 < sides j) ∧
    (∀ j x, inCube n (centers j) (sides j) x → inUnitCube n x) ∧
    (∀ x, inUnitCube n x → ∃ j, inCube n (centers j) (sides j) x) ∧
    (∀ j l x, j ≠ l →
      ¬ (inInterior n (centers j) (sides j) x ∧
         inInterior n (centers l) (sides l) x))

def EventuallyDecomposes (n d : ℕ) : Prop :=
  ∀ k, d ≤ k → Decomposes n k

def IsCubeThreshold (c : ℕ → ℕ) (n : ℕ) : Prop :=
  EventuallyDecomposes n (c n) ∧
    ∀ d, d < c n → ¬ EventuallyDecomposes n d

/-- The numerical lower bound stated by Hadwiger. -/
def hadwigerLower (n : ℕ) : ℕ :=
  2 ^ n + 2 ^ (n - 1)

/-- The Burgess--Erdős upper-bound shape. -/
def burgessErdosUpper (n : ℕ) : ℕ :=
  n ^ (n + 1)

/-- The special upper-bound shape involving 6^n. -/
def hudelsonUpper (n : ℕ) : ℕ :=
  6 ^ n

/-- The general upper-bound shape (2n)^(n-1). -/
def hudelsonGeneralUpper (n : ℕ) : ℕ :=
  (2 * n) ^ (n - 1)

/-- The Connor--Marmorino lower bound. -/
def connorMarmorinoLower (n : ℕ) : ℕ :=
  2 ^ (n + 1) - 1

/-- The numerical upper-bound shape 1.8 n^(n+1). -/
def connorMarmorinoPrimeUpper (n : ℕ) : ℝ :=
  (1.8 : ℝ) * (n : ℝ) ^ (n + 1)

/-- The numerical upper-bound shape e^2 n^n. -/
def connorMarmorinoGeneralUpper (n : ℕ) : ℝ :=
  Real.exp 1 ^ 2 * (n : ℝ) ^ n

def ErdosConjectureAt (c : ℕ → ℕ) (n : ℕ) : Prop :=
  Nat.Prime (n + 1) → c n > n ^ n

theorem witness_pos :
    ErdosConjectureAt (fun _ => 100) 2 := by
  norm_num [ErdosConjectureAt]

theorem witness_neg :
    ¬ ErdosConjectureAt (fun _ => 2) 2 := by
  norm_num [ErdosConjectureAt]

theorem erdos_problem_769 :
    ∀ c : ℕ → ℕ,
      (∀ n, IsCubeThreshold c n) →
        ∀ n, ErdosConjectureAt c n := by
  sorry

end