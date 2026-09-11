import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  Finite simple graphs, with Boolean adjacency.  The source constants
  5, 4, 2, 1, 10, 3, 8, and 21 are retained here; the latter constants
  occur in the surrounding discussion of the problem.
-/

structure FinGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loop : ∀ u, adj u u = false

def degree {n : Nat} (G : FinGraph n) (v : Fin n) : Nat :=
  (Finset.univ.filter (fun w => G.adj v w = true)).card

def differentEdge {n : Nat} (u v x y : Fin n) : Prop :=
  ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))

def closeEdges {n : Nat} (G : FinGraph n) (u v x y : Fin n) : Prop :=
  u = x ∨ u = y ∨ v = x ∨ v = y ∨
    G.adj u x = true ∨ G.adj u y = true ∨
    G.adj v x = true ∨ G.adj v y = true

def StrongEdgeColoring {n k : Nat} (G : FinGraph n)
    (c : Fin n → Fin n → Fin k) : Prop :=
  (∀ u v, G.adj u v = true → c u v = c v u) ∧
  (∀ u v x y,
    G.adj u v = true →
    G.adj x y = true →
    differentEdge u v x y →
    closeEdges G u v x y →
    c u v ≠ c x y)

def ColorableWithin {n : Nat} (G : FinGraph n) (Δ : Nat) : Prop :=
  ∃ k : Fin (5 * Δ ^ 2 + 1),
    4 * k.val ≤ 5 * Δ ^ 2 ∧
      ∃ c : Fin n → Fin n → Fin k.val, StrongEdgeColoring G c

def BoundedColorable {n : Nat} (G : FinGraph n) (Δ : Nat) : Prop :=
  (∀ v, degree G v ≤ Δ) → ColorableWithin G Δ

def emptyGraph (n : Nat) : FinGraph n where
  adj := fun _ _ => false
  symm := by simp
  loop := by simp

def edgeGraph : FinGraph 2 where
  adj := fun u v => if u = v then false else true
  symm := by
    intro u v
    simp [eq_comm]
  loop := by
    intro u
    simp

theorem witness_pos : ColorableWithin (emptyGraph 0) 0 := by
  refine ⟨0, by omega, ?_⟩
  refine ⟨fun u => Fin.elim0 u, ?_⟩
  unfold StrongEdgeColoring
  constructor
  · intro u
    exact Fin.elim0 u
  · intro u
    exact Fin.elim0 u

theorem witness_neg : ¬ ColorableWithin edgeGraph 0 := by
  intro h
  rcases h with ⟨k, hk, c, hc⟩
  have hk0 : k.val = 0 := by
    omega
  have hbad : Fin 0 := by
    simpa [hk0] using c (0 : Fin 2) (0 : Fin 2)
  exact Fin.elim0 hbad

theorem strong_chromatic_index_conjecture :
    ∀ (n : Nat) (G : FinGraph n) (Δ : Nat),
      (∀ v, degree G v ≤ Δ) → ColorableWithin G Δ := by
  sorry

end