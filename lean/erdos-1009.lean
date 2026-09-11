import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

namespace ErdosProblem1009

open Finset

def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

def IsTriangle {n : ℕ} (G : SimpleGraph (Fin n)) (t : Finset (Fin n)) : Prop :=
  t.card = 3 ∧
    ∀ ⦃u v : Fin n⦄, u ∈ t → v ∈ t → u ≠ v → G.Adj u v

def triangleEdges {n : ℕ} (t : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ p.1 ∈ t ∧ p.2 ∈ t)

def IsTrianglePacking {n : ℕ} (G : SimpleGraph (Fin n))
    (P : Finset (Finset (Fin n))) : Prop :=
  (∀ t ∈ P, IsTriangle G t) ∧
    (∀ ⦃s t : Finset (Fin n)⦄, s ∈ P → t ∈ P → s ≠ t →
      Disjoint (triangleEdges s) (triangleEdges t))

theorem erdos_problem_1009 :
    ∀ c : ℝ, 0 < c →
      ∃ f : ℕ, ∀ n k : ℕ, ∀ G : SimpleGraph (Fin n),
        (n ^ 2 / 4 + k ≤ edgeCount G) →
        ((k : ℝ) < c * (n : ℝ)) →
        ∃ P : Finset (Finset (Fin n)),
          IsTrianglePacking G P ∧ k - f ≤ P.card := by
  sorry

end ErdosProblem1009

end
