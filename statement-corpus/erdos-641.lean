/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there some function $f$ such that for all $k\geq 1$ if a finite graph $G$ has chromatic number $\geq f(k)$ then $G$ has $k$ edge disjoint cycles on the same set of vertices?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#641 : [Er92b] [Er97d,p.84] graph theory A problem of Erdős and Hajnal. This was resolved in the negative by Janzer, Steiner, and Sudakov [JSS24] - in fact, this fails even at $k=2$. Janzer, Steiner, and Sudakov proved that there exists a constant $c>0$ such that, for all large $n$, there exists a graph on $n$ vertices with chromatic number\[\geq c\frac{\log\log n}{\log\log \log n}\]which contains no $4$-regular subgraph. Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 22 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #641, https://www.erdosproblems.com/641, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos641

/-- A proper coloring of a finite simple graph by `c` colors. -/
def ProperColoring {V : Type} (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∃ coloring : V → Fin c,
    ∀ ⦃u v : V⦄, G.Adj u v → coloring u ≠ coloring v

/-- The assertion that the chromatic number of `G` is at least `c`, expressed
without introducing a minimum: every coloring with fewer than `c` colors fails. -/
def ChromaticAtLeast {V : Type} (G : SimpleGraph V) (c : ℕ) : Prop :=
  ∀ d < c, ¬ ProperColoring G d

/-- The successor vertex used to describe the cyclic ordering of a cycle. -/
def cycleNext (m : ℕ) (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

/-- A genuinely graph-theoretic cycle: its vertices are distinct and consecutive
vertices, including the final-to-initial pair, are adjacent in `G`. -/
structure GraphCycle {V : Type} (G : SimpleGraph V) where
  length : ℕ
  length_ge_three : 3 ≤ length
  vertices : Fin length → V
  vertices_injective : Function.Injective vertices
  consecutive_adjacent :
    ∀ i : Fin length,
      G.Adj (vertices i) (vertices (cycleNext length
        (Nat.zero_lt_of_lt length_ge_three) i))

/-- The unoriented edge set traversed by a graph cycle. -/
def GraphCycle.UsesEdge {V : Type} {G : SimpleGraph V}
    (C : GraphCycle G) (u v : V) : Prop :=
  ∃ i : Fin C.length,
    (C.vertices i = u ∧
      C.vertices (cycleNext C.length
        (Nat.zero_lt_of_lt C.length_ge_three) i) = v) ∨
    (C.vertices i = v ∧
      C.vertices (cycleNext C.length
        (Nat.zero_lt_of_lt C.length_ge_three) i) = u)

/-- Two cycles have the same vertex set. -/
def GraphCycle.SameVertexSet {V : Type} {G : SimpleGraph V}
    (C D : GraphCycle G) : Prop :=
  ∀ x : V,
    (∃ i, C.vertices i = x) ↔ ∃ j, D.vertices j = x

/-- `HasKEdgeDisjointCycles G k` means that `G` contains `k` cycles whose
vertex sets all agree and whose traversed edge sets are pairwise disjoint. -/
def HasKEdgeDisjointCycles {V : Type} {G : SimpleGraph V} (k : ℕ) : Prop :=
  ∃ cycles : Fin k → GraphCycle G,
    (∀ i j : Fin k, GraphCycle.SameVertexSet (cycles i) (cycles j)) ∧
    (∀ i j : Fin k, i ≠ j →
      ¬ ∃ u v : V,
        GraphCycle.UsesEdge (cycles i) u v ∧
        GraphCycle.UsesEdge (cycles j) u v)

/-- The literal Erdős problem: one function should force the required family of
cycles in every finite graph. -/
def Question641 : Prop :=
  ∃ f : ℕ → ℕ,
    ∀ k : ℕ, 1 ≤ k →
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
        ChromaticAtLeast G (f k) →
        HasKEdgeDisjointCycles k

/-- A proved control showing that the coloring predicate is not vacuous:
an edgeless graph has a one-coloring. -/
theorem edgeless_has_one_coloring {V : Type} [Fintype V] :
    ProperColoring (⊥ : SimpleGraph V) 1 := by
  refine ⟨fun _ => 0, ?_⟩
  intro u v huv h
  have hfalse : False := by
    simpa using huv
  exact hfalse.elim

/-- Resolution of Erdős problem #641. The source records that the proposed
function does not exist, already for `k = 2`; the proof of this literature
result remains to be formalized.

The source clause says: for every `k ≥ 1`, sufficiently large chromatic number
should imply `k` edge-disjoint cycles on one vertex set. The resolution says
this implication fails at `k = 2`, via graphs with no `4`-regular subgraph. -/
theorem resolution_negative : ¬ Question641 := by
  sorry Erdos641

#print axioms Erdos641.edgeless_has_one_coloring
