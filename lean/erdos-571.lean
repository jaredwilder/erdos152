import Mathlib

noncomputable section
open scoped BigOperators
open scoped Classical

namespace TuranConjecture

/-!
The numerical literals occurring in the source include:
571, 74, 78, 75, 78, 30, 81, 84, 91, 713, 3, 2, 1, 4, 5, 18, 21,
20, 22, 23, 2, 1, 3, 4, 5, 2, 1, 2, 3, 1, 2, 1, 1, 2, 7, 5, 2, 1, 2.
-/

/-- A finite graph on the vertex set `Fin n`, represented by its Boolean adjacency
matrix. -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- The graph is simple: it has no loops and adjacency is symmetric. -/
def IsSimple {n : ℕ} (g : Graph n) : Prop :=
  (∀ v, g v v = false) ∧
    (∀ u v, g u v = g v u)

/-- A finite graph is bipartite when its vertices admit a two-colouring such
that every edge has differently coloured endpoints. -/
def IsBipartite {n : ℕ} (g : Graph n) : Prop :=
  ∃ c : Fin n → Bool,
    ∀ u v, g u v = true → c u ≠ c v

/-- The number of directed edges, divided by two for simple graphs. -/
def edgeCount {n : ℕ} (g : Graph n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter
      (fun p => g p.1 p.2 = true)).card / 2

/-- A graph `h` occurs as a not-necessarily-induced subgraph of `g`. -/
def Contains {k n : ℕ} (h : Graph k) (g : Graph n) : Prop :=
  ∃ f : Fin k → Fin n,
    Function.Injective f ∧
      ∀ u v, h u v = true → g (f u) (f v) = true

/-- The finite extremal number associated to a forbidden finite graph. -/
def extremalNumber {k n : ℕ} (h : Graph k) : ℕ :=
  (Finset.univ : Finset (Graph n)).sup
    (fun g => if Contains h g then 0 else edgeCount g)

/-- Two-sided polynomial growth with exponent `α`. -/
def AsympPow {k : ℕ} (h : Graph k) (α : ℚ) : Prop :=
  ∃ c₁ c₂ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧
      ∀ n : ℕ, 1 ≤ n →
        c₁ * Real.rpow (n : ℝ) (α : ℝ) ≤
          (extremalNumber (n := n) h : ℝ) ∧
        (extremalNumber (n := n) h : ℝ) ≤
          c₂ * Real.rpow (n : ℝ) (α : ℝ)

/-- The formalized assertion that `α` is a bipartite Turán exponent. -/
def IsTuranExponent (α : ℚ) : Prop :=
  ∃ k : ℕ, ∃ h : Graph k,
    IsSimple h ∧ IsBipartite h ∧ AsympPow h α

/-- For every rational exponent in the interval `[1,2)`, such a bipartite
graph exists. -/
theorem turan_exponent_conjecture :
    ∀ α : ℚ, 1 ≤ α → α < 2 → IsTuranExponent α := by
  sorry

def edgeGraph2 : Graph 2 :=
  fun u v => if u.val ≠ v.val then true else false

def triangleGraph : Graph 3 :=
  fun u v => if u.val ≠ v.val then true else false

theorem witness_pos : IsBipartite edgeGraph2 := by
  refine ⟨fun u => if u = (0 : Fin 2) then false else true, ?_⟩
  intro u v huv
  fin_cases u <;> fin_cases v <;> simp [edgeGraph2] at huv ⊢

theorem witness_neg : ¬ IsBipartite triangleGraph := by
  intro hb
  rcases hb with ⟨c, hc⟩
  have h01 := hc (0 : Fin 3) 1 (by decide)
  have h02 := hc (0 : Fin 3) 2 (by decide)
  have h12 := hc (1 : Fin 3) 2 (by decide)
  cases e0 : c (0 : Fin 3) <;>
    cases e1 : c (1 : Fin 3) <;>
    cases e2 : c (2 : Fin 3) <;>
    simp_all

end TuranConjecture
end