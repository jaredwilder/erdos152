import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators
open scoped Topology
open Filter

/-- A triangular array of interpolation nodes, with the row indexed by `n`. -/
def NodeSequence := ∀ n : ℕ, Fin n → ℝ

/-- The nodes in a positive row lie in `[-1,1]` and are pairwise distinct. -/
def ValidNodes (n : ℕ) (a : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, a i ∈ Set.Icc (-1 : ℝ) 1) ∧
    (∀ ⦃i j : Fin n⦄, i ≠ j → a i ≠ a j)

/-- Every positive row of a node sequence is a valid set of interpolation nodes. -/
def Admissible (a : NodeSequence) : Prop :=
  ∀ n : ℕ, 0 < n → ValidNodes n (a n)

/-- The Lagrange basis function `p_i^n`; its polynomial degree is `n - 1`. -/
def p (a : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  Finset.prod (Finset.univ.erase i) (fun j => (x - a j) / (a i - a j))

/-- The Lebesgue function associated with one row of interpolation nodes. -/
def lebesgue (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |p a i x|

/-- The Lagrange interpolation operator associated with one row. -/
def lagrange (a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (a i) * p a i x

/-- A sequence has infinite limsup when it exceeds every real level
    frequently along the natural numbers. -/
def LimsupInfinite (u : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, ∃ᶠ n in atTop, C ≤ u n

/-- The first question in the problem statement. -/
def FirstQuestion : Prop :=
  ∃ a : NodeSequence,
    Admissible a ∧
      ∀ f : ℝ → ℝ,
        ContinuousOn f (Set.Icc (-1 : ℝ) 1) →
          ∃ x : ℝ,
            x ∈ Set.Icc (-1 : ℝ) 1 ∧
              LimsupInfinite (fun n : ℕ => lebesgue (a n) x) ∧
                Tendsto (fun n : ℕ => lagrange (a n) f x) atTop (𝓝 (f x))

/-- The second question in the problem statement. -/
def SecondQuestion : Prop :=
  ∃ a : NodeSequence,
    Admissible a ∧
      (∀ x : ℝ,
        x ∈ Set.Icc (-1 : ℝ) 1 →
          LimsupInfinite (fun n : ℕ => lebesgue (a n) x)) ∧
      ∀ f : ℝ → ℝ,
        ContinuousOn f (Set.Icc (-1 : ℝ) 1) →
          ∃ x : ℝ,
            x ∈ Set.Icc (-1 : ℝ) 1 ∧
              Tendsto (fun n : ℕ => lagrange (a n) f x) atTop (𝓝 (f x))

theorem witness_pos : ValidNodes 1 (fun _ : Fin 1 => (0 : ℝ)) := by
  constructor
  · intro i
    change (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1
    norm_num
  · intro i j hij
    fin_cases i
    fin_cases j
    exact False.elim (hij rfl)

theorem witness_neg : ¬ ValidNodes 2 (fun _ : Fin 2 => (0 : ℝ)) := by
  intro h
  have hne :=
    h.2 (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  exact hne rfl

theorem erdos_problem_671 : FirstQuestion ∧ SecondQuestion := by
  sorry

end