import Mathlib


noncomputable section
open scoped BigOperators
/-!
Formalization of Erdős problem 182.

The graph-theoretic predicate below uses finite directed encodings of undirected
simple graphs: validity requires symmetry and absence of loops.
The source literals include 3, 100, 2023, 24, 95, 75, 5, 2, and 1.
-/

abbrev EdgeSet (n : ℕ) := Finset (Fin n × Fin n)

def ValidEdgeSet {n : ℕ} (E : EdgeSet n) : Prop :=
  (∀ v, (v, v) ∉ E) ∧
    ∀ v w, (v, w) ∈ E ↔ (w, v) ∈ E

def EdgeSetDegree {n : ℕ} (E : EdgeSet n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n => (v, w) ∈ E)).card

def HasKRegularSubgraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ E : EdgeSet n,
    ValidEdgeSet E ∧
      (∀ v w, (v, w) ∈ E → G.Adj v w) ∧
      (∀ v, EdgeSetDegree E v = 0 ∨ EdgeSetDegree E v = k) ∧
      (∃ v, EdgeSetDegree E v = k)

def NoKRegularSubgraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ¬ HasKRegularSubgraph G k

def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact
    (Finset.univ.filter
      (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card / 2

theorem witness_pos :
    NoKRegularSubgraph (⊥ : SimpleGraph (Fin 1)) 3 := by
  intro h
  rcases h with ⟨E, _, _, _, v, hv⟩
  have hsub :
      (Finset.univ.filter (fun w : Fin 1 => (v, w) ∈ E)) ⊆
        (Finset.univ : Finset (Fin 1)) := by
    exact Finset.filter_subset _ _
  have hle : EdgeSetDegree E v ≤ 1 := by
    unfold EdgeSetDegree
    calc
      (Finset.univ.filter (fun w : Fin 1 => (v, w) ∈ E)).card ≤
          (Finset.univ : Finset (Fin 1)).card :=
        Finset.card_le_card hsub
      _ = 1 := by simp
  omega

theorem witness_neg :
    ¬ NoKRegularSubgraph (⊤ : SimpleGraph (Fin 4)) 3 := by
  intro h
  apply h
  let E : EdgeSet 4 :=
    Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 ≠ p.2)
  refine ⟨E, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [E, ValidEdgeSet, EdgeSetDegree] <;>
    native_decide

theorem main_conjecture :
    ∀ k : ℕ, 3 ≤ k →
      ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 100 ≤ n →
          ∀ G : SimpleGraph (Fin n),
            C * (n : ℝ) * Real.log (Real.log (n : ℝ))
                ≤ (edgeCount G : ℝ) →
              HasKRegularSubgraph G k := by
  sorry

end