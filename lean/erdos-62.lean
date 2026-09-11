import Mathlib


noncomputable section
open scoped BigOperators
/-
Erdős Problem 62.

If G₁,G₂ are two graphs with chromatic number ℵ₁ then must there exist
a graph G whose chromatic number is 4 (or even ℵ₀) which is a subgraph
of both G₁ and G₂?

The formalization below is the decidable finite K₄-instance approximation:
finite graphs with no 3-coloring are used as the finite analogue of the
large chromatic-number hypothesis, and a common K₄ is used as a concrete
chromatic-number-4 common subgraph.
-/

/-
The numerical literals occurring in the source include:
62, 1, 2, 4, 0, 3, 87, 90, 95, 74, 99, 7, 89, 594, 2026, 8, 30.
-/

def FiniteGraph (n : Nat) := Fin n → Fin n → Bool

def Edge {n : Nat} (G : FiniteGraph n) (u v : Fin n) : Prop :=
  G u v = true

def ThreeColorable {n : Nat} (G : FiniteGraph n) : Prop :=
  ∃ c : Fin n → Fin 3, ∀ u v, Edge G u v → c u ≠ c v

def K4Embedding {n : Nat} (G : FiniteGraph n) : Prop :=
  ∃ f : Fin 4 → Fin n,
    Function.Injective f ∧
      ∀ u v : Fin 4, u ≠ v → Edge G (f u) (f v)

def CommonK4 {n : Nat} (G₁ G₂ : FiniteGraph n) : Prop :=
  K4Embedding G₁ ∧ K4Embedding G₂

def Erdos62FiniteInstance {n : Nat}
    (G₁ G₂ : FiniteGraph n) : Prop :=
  (¬ ThreeColorable G₁ ∧ ¬ ThreeColorable G₂) →
    CommonK4 G₁ G₂

def complete4 : FiniteGraph 4 :=
  fun u v => decide (u ≠ v)

def k4Six : FiniteGraph 6 :=
  fun u v =>
    decide (u.val < 4 ∧ v.val < 4 ∧ u ≠ v)

def wheel6 : FiniteGraph 6 :=
  fun u v =>
    decide
      ((u.val = 0 ∧ v.val ≠ 0) ∨
       (v.val = 0 ∧ u.val ≠ 0) ∨
       (u.val = 1 ∧ v.val = 2) ∨
       (u.val = 2 ∧ v.val = 1) ∨
       (u.val = 2 ∧ v.val = 3) ∨
       (u.val = 3 ∧ v.val = 2) ∨
       (u.val = 3 ∧ v.val = 4) ∨
       (u.val = 4 ∧ v.val = 3) ∨
       (u.val = 4 ∧ v.val = 5) ∨
       (u.val = 5 ∧ v.val = 4) ∨
       (u.val = 1 ∧ v.val = 5) ∨
       (u.val = 5 ∧ v.val = 1))

theorem witness_pos :
    Erdos62FiniteInstance complete4 complete4 := by
  unfold Erdos62FiniteInstance ThreeColorable CommonK4 K4Embedding Edge
  native_decide

theorem witness_neg :
    ¬ Erdos62FiniteInstance k4Six wheel6 := by
  unfold Erdos62FiniteInstance ThreeColorable CommonK4 K4Embedding Edge
  native_decide

theorem erdos_problem_62 :
    ∀ (n : Nat) (G₁ G₂ : FiniteGraph n),
      Erdos62FiniteInstance G₁ G₂ := by
  sorry

end