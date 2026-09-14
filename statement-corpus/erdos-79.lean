/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
We say $G$ is Ramsey size linear if $R(G,H)\ll m$ for all graphs $H$ with $m$ edges and no isolated vertices. Are there infinitely many graphs $G$ which are not Ramsey size linear but such that all of its subgraphs are?
-/

/- 
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#79 : [EFRS93] [Er95] graph theory | ramsey theory Asked by Erdős, Faudree, Rousseau, and Schelp [EFRS93] . $K_4$ is the only known example of such a graph. Wigderson [Wi24] has proved that there are infinitely many such graphs (although his proof is not explicit, and an explicit example of such a graph apart from $K_4$ is still unknown). Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #79, https://www.erdosproblems.com/79, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos079

/-- A finite simple graph, represented by a simple graph on the canonical finite vertex set
`Fin order`.  The carrier is the actual Mathlib `SimpleGraph`, rather than a classification tag. -/
structure FiniteGraph where
  order : ℕ
  graph : SimpleGraph (Fin order)

/-- The number of directed adjacent pairs.  This differs from the conventional edge count by
a factor of two for loopless undirected graphs, which is harmless for a linear bound. -/
def edgeCount (G : FiniteGraph) : ℕ :=
  Finset.card
    (Finset.filter
      (fun p : Fin G.order × Fin G.order => G.graph.Adj p.1 p.2)
      Finset.univ)

/-- A graph has no isolated vertices when every vertex has an adjacent vertex. -/
def NoIsolated (G : FiniteGraph) : Prop :=
  ∀ v : Fin G.order, ∃ w : Fin G.order, G.graph.Adj v w

/-- `IsSubgraph H G` means that `H` is a subgraph of `G`: its vertices inject into those of `G`
and every edge of `H` maps to an edge of `G`.  Thus the first argument is the subgraph and the
second argument is the host. -/
def IsSubgraph (H G : FiniteGraph) : Prop :=
  ∃ f : Fin H.order → Fin G.order,
    Function.Injective f ∧
      ∀ ⦃u v : Fin H.order⦄, H.graph.Adj u v → G.graph.Adj (f u) (f v)

/-- The empty-edge graph on `n` vertices. -/
def nullGraph (n : ℕ) : FiniteGraph :=
  ⟨n, ⊥⟩

/-- A proved asymmetric direction control for the subgraph relation: the zero-vertex graph is a
subgraph of the one-vertex graph, but the converse is impossible.  This fixes the argument order
independently of reflexivity. -/
theorem subgraph_direction_control :
    IsSubgraph (nullGraph 0) (nullGraph 1) ∧
      ¬ IsSubgraph (nullGraph 1) (nullGraph 0) := by
  constructor
  · refine ⟨(fun x => Fin.elim0 x), ?_, ?_⟩
    · intro x
      exact Fin.elim0 x
    · intro u v huv
      exact Fin.elim0 u
  · rintro ⟨f, hf, hadj⟩
    exact Fin.elim0 (f 0)

/-- The directed edge count of a null graph is zero. -/
theorem edgeCount_null (n : ℕ) : edgeCount (nullGraph n) = 0 := by
  classical
  simp [edgeCount, nullGraph]

/-- The Ramsey number function intended by the source.  Its standard coloring-theoretic
definition is not yet formalized here; this explicit named gap is retained rather than replacing
the Ramsey number by an uninterpretable label. -/
noncomputable def ramseyNumber : FiniteGraph → FiniteGraph → ℕ := by
  sorry

/-- `RamseySizeLinear R G` formalizes the displayed asymptotic condition using the supplied Ramsey
number function `R`: there is one constant bounding `R G H` linearly in the edge count of every
finite graph `H` with no isolated vertices.  The precise conventional normalization of `R` is
part of the remaining Ramsey-number formalization gap. -/
def RamseySizeLinear (R : FiniteGraph → FiniteGraph → ℕ) (G : FiniteGraph) : Prop :=
  ∃ C : ℕ, ∀ H : FiniteGraph, NoIsolated H → R G H ≤ C * edgeCount H

/-- The source's question, read as unboundedly many finite graphs (hence infinitely many), with
the graph order used to witness infinitude.  It asks for graphs which are not Ramsey size linear
while every subgraph, in the explicitly defined embedding sense, is Ramsey size linear. -/
def WigdersonQuestion (R : FiniteGraph → FiniteGraph → ℕ) : Prop :=
  ∀ N : ℕ, ∃ G : FiniteGraph,
    N < G.order ∧
      ¬ RamseySizeLinear R G ∧
        ∀ H : FiniteGraph, IsSubgraph H G → RamseySizeLinear R H

/-- Resolution node n001: Wigderson's result, as recorded in the source, asserts the question.
The proof remains an explicit gap because the coloring-theoretic definition of the Ramsey number
and Wigderson's non-explicit construction have not been formalized in this artifact. -/
theorem wigderson_resolution :
    WigdersonQuestion ramseyNumber := by
  sorry Erdos079
