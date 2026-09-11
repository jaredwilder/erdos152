import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
-- The source entry is Erdős Problem 184.  The numerical references appearing in
-- the source include 184, 66, 71, 76, 81, 83, 5, 3, 1, 22, 2, 14, 583,
-- 1017, and 2026-08-30; the graph-theoretic statement uses n, O(n), and n-3.

namespace Erdos184

/-- An edge of a simple graph on `Fin n`, represented with its endpoints ordered. -/
def Edge (n : Nat) := {e : Fin n × Fin n // e.1 < e.2}

instance (n : Nat) : DecidableEq (Edge n) := inferInstance

def incident {n : Nat} (v : Fin n) (e : Edge n) : Prop :=
  e.1.1 = v ∨ e.1.2 = v

instance {n : Nat} (v : Fin n) : DecidablePred (incident v) := by
  intro e
  unfold incident
  infer_instance

def degree {n : Nat} (p : Finset (Edge n)) (v : Fin n) : Nat :=
  (p.filter (incident v)).card

def TwoRegular {n : Nat} (p : Finset (Edge n)) : Prop :=
  ∀ v : Fin n, degree p v = 0 ∨ degree p v = 2

/--
A cycle is a nonempty inclusion-minimal edge set in which every vertex has
degree zero or two.  For finite simple graphs this is the usual notion of a
single graph-theoretic cycle.
-/
def IsCycle {n : Nat} (p : Finset (Edge n)) : Prop :=
  p.Nonempty ∧
    TwoRegular p ∧
    ∀ q ∈ p.powerset, q.Nonempty → TwoRegular q → q = p

def IsCycleOrEdge {n : Nat} (p : Finset (Edge n)) : Prop :=
  p.card = 1 ∨ IsCycle p

/-- A decomposition into edge-disjoint cycles and singleton edges. -/
def IsDecomposition {n : Nat} (G : Finset (Edge n))
    (pieces : Finset (Finset (Edge n))) : Prop :=
  (∀ p ∈ pieces, IsCycleOrEdge p) ∧
    (∀ p ∈ pieces, ∀ q ∈ pieces, p ≠ q → Disjoint p q) ∧
    pieces.biUnion (fun p => p) = G

/-- Decomposability with an explicit linear bound `C * n` on the number of pieces. -/
def LinearAtMost {n : Nat} (G : Finset (Edge n)) (C : Nat) : Prop :=
  ∃ pieces : Finset (Finset (Edge n)),
    IsDecomposition G pieces ∧ pieces.card ≤ C * n

theorem witness_pos :
    LinearAtMost (n := 3) (∅ : Finset (Edge 3)) 0 := by
  refine ⟨∅, ?_, ?_⟩
  · simp [IsDecomposition]
  · simp

def e01 : Edge 3 :=
  ⟨(0, 1), by decide⟩

theorem witness_neg :
    ¬ LinearAtMost (n := 3) ({e01} : Finset (Edge 3)) 0 := by
  intro h
  rcases h with ⟨pieces, hdec, hcard⟩
  have hcard0 : pieces.card = 0 := by
    omega
  have hpieces : pieces = ∅ := Finset.card_eq_zero.mp hcard0
  have hEq : pieces.biUnion (fun p => p) = ({e01} : Finset (Edge 3)) :=
    hdec.2.2
  rw [hpieces] at hEq
  simpa using hEq

/--
Any graph on `n` vertices can be decomposed into `O(n)` many
cycles and edges.
-/
theorem erdos_184 :
    ∃ C : Nat, ∀ n : Nat, ∀ G : Finset (Edge n), LinearAtMost G C := by
  sorry

end Erdos184

end