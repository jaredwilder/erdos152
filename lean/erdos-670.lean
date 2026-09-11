import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-- A point of `ℝ^d`, represented by its coordinates. -/
def Point (d : ℕ) := Fin d → ℝ

/-- Euclidean distance between two points of `ℝ^d`. -/
def euclideanDistance {d : ℕ} (x y : Point d) : ℝ :=
  Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2)

/-- All distinct pairs of points have distances differing by at least `1`. -/
def PairwiseSeparated {d n : ℕ} (A : Fin n → Point d) : Prop :=
  ∀ i j k l : Fin n,
    i < j →
    k < l →
    (i, j) ≠ (k, l) →
    |euclideanDistance (A i) (A j) -
        euclideanDistance (A k) (A l)| ≥ 1

/-- The diameter of a finite configuration. -/
def diameter {d n : ℕ} (A : Fin n → Point d) : ℝ :=
  sSup (Set.range (fun p : Fin n × Fin n =>
    euclideanDistance (A p.1) (A p.2)))

/--
The fixed-dimensional asymptotic assertion from Erdos problem 670.
The `ε`-formulation expresses the lower bound `(1 + o(1)) n^2`.
-/
def Erdos670Claim : Prop :=
  ∀ d : ℕ,
    ∀ A : ∀ n : ℕ, Fin n → Point d,
      ∀ ε : ℝ,
        0 < ε →
        ∃ N : ℕ,
          ∀ n : ℕ,
            N ≤ n →
            Function.Injective (A n) →
            PairwiseSeparated (A n) →
            (1 - ε) * (n : ℝ) ^ 2 ≤ diameter (A n)

/-- The conjectured fixed-dimensional lower bound. -/
theorem erdos_670 : Erdos670Claim := by
  sorry

/-- Two distinct points in `ℝ^1` form a separated configuration. -/
theorem witness_pos :
    Function.Injective
        (fun i : Fin 2 => (fun _ : Fin 1 => if i = 0 then (0 : ℝ) else 1)) ∧
      PairwiseSeparated
        (fun i : Fin 2 => (fun _ : Fin 1 => if i = 0 then (0 : ℝ) else 1)) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · have h := congrFun hij (0 : Fin 1)
      norm_num at h
    · have h := congrFun hij (0 : Fin 1)
      norm_num at h
    · rfl
  · intro i j k l hij hkl hne
    have hpair : (i, j) = (k, l) := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
        simp_all
    exact (hne hpair).elim

/-- A repeated point is not a configuration of distinct points. -/
theorem witness_neg :
    ¬(Function.Injective
        (fun _ : Fin 3 => (fun _ : Fin 1 => (0 : ℝ))) ∧
      PairwiseSeparated
        (fun _ : Fin 3 => (fun _ : Fin 1 => (0 : ℝ)))) := by
  intro h
  have h01 : (0 : Fin 3) = 1 := h.1 rfl
  norm_num at h01

end