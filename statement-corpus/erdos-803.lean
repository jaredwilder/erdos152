/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
We call a graph $H$ $D$-balanced (or $D$-almost-regular) if the maximum degree of $H$ is at most $D$ times the minimum degree of $H$. Is it true that for every $m\geq 1$, if $n$ is sufficiently large, any graph on $n$ vertices with $\geq n\log n$ edges contains a $O(1)$-balanced subgraph with $m$ vertices and $\gg m\log m$ edges (where the implied constants are absolute)?

NODE n001-resolution (resolution), VERBATIM:
#803 : [ErSi70] graph theory A problem of Erdős and Simonovits [ErSi70] , who proved a similar claim replacing $\log n$ and $\log m$ by $n^{c}$ and $m^c$ respectively, for any constant $c>0$ (where the balance parameter may depend on $c$). (See [1077] .) Alon [Al08] proved this is false: for every $D>1$ and large $n$ there is a graph $G$ with $n$ vertices and $\geq n\log n$ edges such that if $H$ is a $D$-balanced subgraph then $H$ has $\ll m\sqrt{\log m}+\log D$ many edges. Janzer and Sudakov [JaSu23] have proved that, for any $k$, if $n$ is sufficiently large then any graph on $n$ vertices with at least $n\log n$ edges contains an $O(1)$-balanced subgraph on $m\geq k$ vertices with\[\gg_k \frac{\sqrt{\log m}}{(\log\log m)^{3/2}}m\]many edges. See also [1077] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 07 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #803, https://www.erdosproblems.com/803, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos803

/-- The number of edges of a finite simple graph, computed by counting ordered
adjacent pairs and dividing by two. -/
def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Fintype.card {p : V × V // G.Adj p.1 p.2} / 2

/-- POSITIVE WITNESS: the complete graph on three vertices has three edges. -/
theorem edgeCount_witness_pos :
    edgeCount (⊤ : SimpleGraph (Fin 3)) = 3 := by
  decide

/-- NEGATIVE WITNESS: the empty graph on three vertices has zero edges, a
near-miss obtained by deleting all three edges from the positive witness. -/
theorem edgeCount_witness_neg :
    edgeCount (⊥ : SimpleGraph (Fin 3)) = 0 := by
  decide

/-- A graph is dense in the threshold used by the source when its edge count is
at least `n * log n`. -/
def DenseGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  edgeCount G ≥ n * Nat.log n

/-- POSITIVE WITNESS: the complete graph on three vertices satisfies the
density threshold `3 * log 3 = 3`. -/
theorem DenseGraph_witness_pos :
    DenseGraph (⊤ : SimpleGraph (Fin 3)) := by
  decide

/-- NEGATIVE WITNESS: the empty graph on three vertices fails the density
threshold, while keeping the same number of vertices. -/
theorem DenseGraph_witness_neg :
    ¬ DenseGraph (⊥ : SimpleGraph (Fin 3)) := by
  decide

/-- The degree of a vertex in a finite simple graph. -/
def vertexDegree {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  Fintype.card {w : V // G.Adj v w}

/-- A graph is `D`-balanced when every vertex degree is at most `D` times
every vertex degree. This is equivalent to maximum degree at most `D` times
minimum degree, and makes the direction of the balance inequality explicit. -/
def Balanced {V : Type} [Fintype V] (D : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ u v : V, vertexDegree G u ≤ D * vertexDegree G v

/-- POSITIVE WITNESS: the complete graph on three vertices is `1`-balanced. -/
theorem Balanced_witness_pos :
    Balanced 1 (⊤ : SimpleGraph (Fin 3)) := by
  decide

/-- NEGATIVE WITNESS: changing the balance parameter from `1` to `0` makes
the complete graph on three vertices fail exactly the balance condition. -/
theorem Balanced_witness_neg :
    ¬ Balanced 0 (⊤ : SimpleGraph (Fin 3)) := by
  decide

/-- `BalancedDenseSubgraphExists G m D C` says that `G` has an induced
subgraph on exactly `m` vertices which is `D`-balanced and has at least
`C * m * log m` edges. The induced graph is taken on the subtype of a
finite vertex set, so this is a decidable finite-instance formulation. -/
def BalancedDenseSubgraphExists {n : ℕ} (G : SimpleGraph (Fin n))
    (m D C : ℕ) : Prop :=
  ∃ S : Finset (Fin n),
    S.card = m ∧
      Balanced D (G.induce (S : Set (Fin n))) ∧
        edgeCount (G.induce (S : Set (Fin n))) ≥ C * m * Nat.log m

/-- POSITIVE WITNESS: the complete graph on three vertices itself is a
`1`-balanced subgraph with three vertices and at least `3 * log 3` edges. -/
theorem BalancedDenseSubgraphExists_witness_pos :
    BalancedDenseSubgraphExists (⊤ : SimpleGraph (Fin 3)) 3 1 1 := by
  decide

/-- NEGATIVE WITNESS: the empty graph on three vertices is a near miss with
the same vertex set and balance parameter, but has no required edges. -/
theorem BalancedDenseSubgraphExists_witness_neg :
    ¬ BalancedDenseSubgraphExists (⊥ : SimpleGraph (Fin 3)) 3 1 1 := by
  decide

/-- Alon's resolution of the source question, expressed using the finite
encoding above. The source asks whether there are absolute constants giving
balanced subgraphs with order `m * log m` edges for every sufficiently large
dense graph; its resolution says this assertion is false. The formal statement
below leaves the asymptotic counterexample construction as an honest gap. -/
theorem alon_resolution :
    ¬ (∃ D C : ℕ,
        1 < D ∧ 0 < C ∧
          ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N,
            ∀ G : SimpleGraph (Fin n),
              DenseGraph G →
                BalancedDenseSubgraphExists G m D C) := by
  sorry Erdos803

#print axioms Erdos803.edgeCount_witness_pos
#print axioms Erdos803.edgeCount_witness_neg
#print axioms Erdos803.DenseGraph_witness_pos
#print axioms Erdos803.DenseGraph_witness_neg
#print axioms Erdos803.Balanced_witness_pos
#print axioms Erdos803.Balanced_witness_neg
#print axioms Erdos803.BalancedDenseSubgraphExists_witness_pos
#print axioms Erdos803.BalancedDenseSubgraphExists_witness_neg
