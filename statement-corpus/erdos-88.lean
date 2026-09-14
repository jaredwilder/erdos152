/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
For any $\epsilon>0$ there exists $\delta=\delta(\epsilon)>0$ such that if $G$ is a graph on $n$ vertices with no independent set or clique of size $\geq \epsilon\log n$ then $G$ contains an induced subgraph with $m$ edges for all $m\leq \delta n^2$.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#88 : [Er92b] [Er95] [Er97d] graph theory | ramsey theory Conjectured by Erdős and McKay, who proved it with $\delta n^2$ replaced by $\delta (\log n)^2$. Solved by Kwan, Sah, Sauermann, and Sawhney [KSSS22] . Erdős' original formulation also had the condition that $G$ has $\gg n^2$ edges, but an old result of Erdős and Szemerédi says that this follows from the other condition anyway. Additional thanks to : Zachary Hunter and Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #88, https://www.erdosproblems.com/88, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




-- @category research solved

import Mathlib
namespace Erdos88

/-- A finite vertex set is independent when every two distinct vertices in it are nonadjacent. -/
def IsIndependentSet {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → u ≠ v → ¬ G.Adj u v

/-- A finite vertex set is a clique when every two distinct vertices in it are adjacent. -/
def IsCliqueSet {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, u ∈ s → v ∈ s → u ≠ v → G.Adj u v

/-- The predicate that a vertex set is an independent set of the threshold size from the source. -/
def HasLargeIndependentSet {n : ℕ} (G : SimpleGraph (Fin n))
    (ε : ℝ) (s : Finset (Fin n)) : Prop :=
  (ε * Real.log (n : ℝ) ≤ (s.card : ℝ)) ∧ IsIndependentSet G s

/-- The predicate that a vertex set is a clique of the threshold size from the source. -/
def HasLargeClique {n : ℕ} (G : SimpleGraph (Fin n))
    (ε : ℝ) (s : Finset (Fin n)) : Prop :=
  (ε * Real.log (n : ℝ) ≤ (s.card : ℝ)) ∧ IsCliqueSet G s

/-- The number of edges in the subgraph induced by a finite vertex set. -/
noncomputable def InducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : ℕ :=
  by
    classical
    exact ((G.induce (s : Set (Fin n))).edgeFinset).card

/-- The formalized statement of Erdős Problem 88, using finite simple graphs on `Fin n`. -/
def Erdos88Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
        (∀ s : Finset (Fin n),
          ¬ (HasLargeIndependentSet G ε s ∨ HasLargeClique G ε s)) →
        ∀ m : ℕ, (m : ℝ) ≤ δ * (n : ℝ) ^ 2 →
          ∃ s : Finset (Fin n), InducedEdgeCount G s = m

/-- The empty induced subgraph has zero edges, providing a proved control for the formalization. -/
theorem inducedEdgeCount_empty {n : ℕ} (G : SimpleGraph (Fin n)) :
    InducedEdgeCount G (∅ : Finset (Fin n)) = 0 := by
  classical
  simp [InducedEdgeCount]

#print axioms inducedEdgeCount_empty

end Erdos88
