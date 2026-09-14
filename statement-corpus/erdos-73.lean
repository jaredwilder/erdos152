/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size $\geq (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ be the union of a bipartite graph and $O_k(1)$ many vertices?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#73 : [EHS82] [Er94b] [Er95] [Er96] [Er97d] graph theory Proved by Reed [Re99] . (Thanks also to Reed for pointing out that the case $k=0$ is trivial, since if $G$ is not bipartite then $G$ contains an odd cycle.) See also [922] and the entry in the graphs problem collection . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #73, https://www.erdosproblems.com/73, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem73

/-- A finite simple undirected graph represented by a finite vertex type `Fin n`. -/
structure FiniteGraph where
  n : ℕ
  edge : Fin n → Fin n → Prop
  symmetric : ∀ ⦃u v : Fin n⦄, edge u v → edge v u
  loopless : ∀ ⦃u : Fin n⦄, ¬ edge u u

/-- A set of vertices is independent when it contains no adjacent distinct vertices. -/
def IsIndependent (G : FiniteGraph) (S : Finset (Fin G.n)) : Prop :=
  ∀ ⦃u v : Fin G.n⦄, u ∈ S → v ∈ S → G.edge u v → u = v

/-- 
The hereditary independent-set hypothesis from the source.

For every induced subgraph on a vertex set `S`, there is an independent subset
`I` satisfying `2 * |I| + k ≥ |S|`, which is the natural integer form of
`|I| ≥ (|S| - k) / 2`.
-/
def HasIndependentSetBound (G : FiniteGraph) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin G.n),
    ∃ I : Finset (Fin G.n),
      I ⊆ S ∧ IsIndependent G I ∧ 2 * I.card + k ≥ S.card

/-- 
The graph obtained after deleting `D` is bipartite, expressed by a two-colouring
of the remaining vertices.
-/
def IsBipartiteAfter (G : FiniteGraph) (D : Finset (Fin G.n)) : Prop :=
  ∃ c : Fin G.n → Bool,
    ∀ ⦃u v : Fin G.n⦄,
      u ∉ D →
      v ∉ D →
      G.edge u v →
      c u ≠ c v

/-- 
Formalisation of the source question.

The source says: “Must `G` be the union of a bipartite graph and `O_k(1)`
many vertices?”  Here `D` is the exceptional vertex set, bounded by a
constant `C` depending only on `k`, and the induced graph outside `D` is
required to be bipartite.  The source records this statement as proved by
Reed; this declaration records the corresponding proposition.
-/
def Erdos73Statement : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ G : FiniteGraph,
    HasIndependentSetBound G k →
      ∃ D : Finset (Fin G.n),
        D.card ≤ C ∧ IsBipartiteAfter G D

/-- 
The resolution recorded by the source is that `Erdos73Statement` is true,
with the proof attributed to Reed [Re99].  This declaration preserves the
resolved proposition without introducing an unproved theorem into the kernel.
-/
def ReedResolution : Prop :=
  Erdos73Statement

/-- 
A proved control exercising the deletion and bipartiteness definitions:
deleting all vertices always leaves a bipartite graph, with the explicit
bound `|V(G)|`.
-/
theorem deletion_control (G : FiniteGraph) :
    ∃ D : Finset (Fin G.n),
      D.card ≤ G.n ∧ IsBipartiteAfter G D := by
  refine ⟨Finset.univ, ?_, ?_⟩
  · simp
  · refine ⟨fun _ => false, ?_⟩
    intro u v hu hv h
    simp at hu

#print axioms deletion_control

end ErdosProblem73