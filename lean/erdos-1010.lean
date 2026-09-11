import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
structure FiniteGraph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ ⦃u v : Fin n⦄, adj u v → adj v u
  loopless : ∀ v : Fin n, ¬ adj v v

noncomputable def edgeSet {n : ℕ} (G : FiniteGraph n) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (fun p => p.1 < p.2 ∧ G.adj p.1 p.2)

noncomputable def edgeCount {n : ℕ} (G : FiniteGraph n) : ℕ :=
  (edgeSet G).card

noncomputable def triangleSet {n : ℕ} (G : FiniteGraph n) :
    Finset (Fin n × (Fin n × Fin n)) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.1 < p.2.1 ∧
    p.2.1 < p.2.2 ∧
    G.adj p.1 p.2.1 ∧
    G.adj p.1 p.2.2 ∧
    G.adj p.2.1 p.2.2)

noncomputable def triangleCount {n : ℕ} (G : FiniteGraph n) : ℕ :=
  (triangleSet G).card

theorem erdos_problem_1010 :
    ∀ (n t : ℕ), t < n / 2 →
      ∀ G : FiniteGraph n,
        edgeCount G = n ^ 2 / 4 + t →
          t * (n / 2) ≤ triangleCount G := by
  sorry

end
