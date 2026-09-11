import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter
/-
  Source literals retained from the entry: #725, Er81, ErKa46, Ya51,
  k = o((log n)^(3/2-ε)), and k ≤ n^(1/3-o(1)).
-/

def IsLatinRectangle (k n : ℕ) (r : Fin k → Fin n → Fin n) : Prop :=
  (∀ i, Function.Bijective (r i)) ∧
    (∀ j, Function.Injective (fun i => r i j))

def latinRectangleCount (k n : ℕ) : ℕ :=
  Fintype.card {r : Fin k → Fin n → Fin n // IsLatinRectangle k n r}

def expectedLatinRectangleCount (k n : ℕ) : ℝ :=
  Real.exp (-((Nat.choose k 2 : ℕ) : ℝ)) *
    (((Nat.factorial n : ℕ) : ℝ) ^ k)

def LittleOAtTop (f g : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => f n / g n) atTop (𝓝 0)

def EquivalentAtTop (f g : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => f n / g n) atTop (𝓝 1)

def YamamotoRegime (k : ℕ → ℕ) : Prop :=
  ∃ a : ℕ → ℝ,
    Tendsto a atTop (𝓝 0) ∧
      ∀ᶠ n in atTop,
        (k n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 3 - a n)

def oneByOne : Fin 1 → Fin 1 → Fin 1 :=
  fun _ _ => 0

def twoByOne : Fin 2 → Fin 1 → Fin 1 :=
  fun _ _ => 0

theorem witness_pos : IsLatinRectangle 1 1 oneByOne := by
  unfold IsLatinRectangle
  constructor
  · intro i
    fin_cases i
    constructor
    · intro a b _
      exact Subsingleton.elim _ _
    · intro b
      refine ⟨0, ?_⟩
      fin_cases b
      rfl
  · intro j
    intro i i' _
    exact Subsingleton.elim _ _

theorem witness_neg : ¬ IsLatinRectangle 2 1 twoByOne := by
  intro h
  have hEq : (0 : Fin 2) = 1 := by
    apply (h.2 (0 : Fin 1))
    rfl
  have hv : (0 : ℕ) = 1 := congrArg Fin.val hEq
  omega

theorem asymptotic_formula :
    ∀ (k : ℕ → ℕ) (ε : ℝ),
      0 < ε →
        (LittleOAtTop
            (fun n : ℕ => (k n : ℝ))
            (fun n : ℕ => (Real.log n) ^ ((3 : ℝ) / 2 - ε)) →
          EquivalentAtTop
            (fun n : ℕ => (latinRectangleCount (k n) n : ℝ))
            (fun n : ℕ => expectedLatinRectangleCount (k n) n)) ∧
        (YamamotoRegime k →
          EquivalentAtTop
            (fun n : ℕ => (latinRectangleCount (k n) n : ℝ))
            (fun n : ℕ => expectedLatinRectangleCount (k n) n)) := by
  sorry

end