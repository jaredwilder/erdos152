import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

structure ExtGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def IsBipartite {n : ℕ} (G : ExtGraph n) : Prop :=
  ∃ color : Fin n → Bool,
    ∀ ⦃u v : Fin n⦄, G.adj u v = true → color u ≠ color v

def IsDegenerate {n r : ℕ} (G : ExtGraph n) (r : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty →
    ∃ v : Fin n, v ∈ S ∧
      (S.filter (fun w => G.adj v w = true)).card ≤ r

def ContainsAsSubgraph {h n : ℕ} (H : ExtGraph h) (G : ExtGraph n) : Prop :=
  ∃ f : Fin h → Fin n,
    Function.Injective f ∧
      ∀ ⦃u v : Fin h⦄, H.adj u v = true → G.adj (f u) (f v) = true

def HFree {h n : ℕ} (H : ExtGraph h) (G : ExtGraph n) : Prop :=
  ¬ ContainsAsSubgraph H G

def edgeCount {n : ℕ} (G : ExtGraph n) : ℕ :=
  ∑ u : Fin n,
    (Finset.univ.filter
      (fun v : Fin n => u < v ∧ G.adj u v = true)).card

theorem erdos_simonovits_conjecture
    {h r : ℕ} (H : ExtGraph h) (hr : 0 < r)
    (hb : IsBipartite H) (hd : IsDegenerate (r := r) H r) :
    ∃ C : ℝ, 0 < C ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∀ G : ExtGraph n, HFree H G →
          (edgeCount G : ℝ) ≤
            C * Real.rpow (n : ℝ) (2 - (1 : ℝ) / (r : ℝ)) := by
  sorry

end