/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Suppose $G$ is a graph on $n$ vertices which contains no complete graph or independent set on $\gg \log n$ many vertices. Must $G$ contain $\gg n^{5/2}$ induced subgraphs which pairwise differ in either the number of vertices or the number of edges?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#636 : [Er93,p.346] [Er97d] graph theory | ramsey theory A problem of Erdős, Faudree, and Sós, who proved there exist $\gg n^{3/2}$ many such subgraphs, and note that $n^{5/2}$ would be best possible. (Although in [Er93] Erdős credits this question to Alon and Bollobás.) This was proved by Kwan and Sudakov [KwSu21] . Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #636, https://www.erdosproblems.com/636, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos636

/-- A clique in a finite simple graph, represented by a set of vertices. -/
def IsClique {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → G.Adj u v

/-- An independent set in a finite simple graph, represented by a set of vertices. -/
def IsIndependent {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.Adj u v

/-- The number of edges in the subgraph induced by `S`.

The ordered pairs of adjacent vertices are counted and divided by two; loops
are absent because `G` is a simple graph. -/
def inducedEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((S.product S).filter (fun p => G.Adj p.1 p.2)).card / 2

/-- Two induced subgraphs differ when their numbers of vertices or edges differ. -/
def DifferInSizeOrEdges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S T : Finset V) : Prop :=
  S.card ≠ T.card ∨ inducedEdgeCount G S ≠ inducedEdgeCount G T

/-- A family of vertex subsets whose induced subgraphs pairwise differ in size
or in number of edges. -/
def SeparatingFamily {V : Type*} [Fintype V] (G : SimpleGraph V)
    (F : Finset (Finset V)) : Prop :=
  ∀ ⦃S T : Finset V⦄, S ∈ F → T ∈ F → S ≠ T → DifferInSizeOrEdges G S T

/-- The Ramsey restriction used in the formalization: there is no clique and no
independent set of size at least `r`. -/
def RamseySparse {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ S : Finset V, r ≤ S.card → ¬ IsClique G S ∧ ¬ IsIndependent G S

/-- The formalized question and its resolution.

Here `≫ log n` is made explicit as `C * Nat.log 2 n` for some positive
constant `C`, and `≫ n^(5/2)` is represented on natural numbers by
`c * n^2 * Nat.sqrt n` for some positive constant `c`.  This is the standard
discrete proxy for the asymptotic exponent, and is stated explicitly rather
than silently treating `≫` as a primitive Lean notion. -/
def Question636 : Prop :=
  ∃ c C N : ℕ, 0 < c ∧ 0 < C ∧
    ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        RamseySparse G (C * Nat.log 2 n) →
          ∃ F : Finset (Finset (Fin n)),
            SeparatingFamily G F ∧
              c * n ^ 2 * Nat.sqrt n ≤ F.card

/-- A proved control showing that the file's family predicate is not
inconsistent: the empty family is separating for every finite graph. -/
theorem emptyFamily_separating {V : Type*} [Fintype V] (G : SimpleGraph V) :
    SeparatingFamily G ∅ := by
  simp [SeparatingFamily]

/-- A proved control for the induced-edge-count definition at the empty
vertex set. -/
theorem inducedEdgeCount_empty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    inducedEdgeCount G ∅ = 0 := by
  simp [inducedEdgeCount]

/-- The result recorded in the resolution node: Kwan and Sudakov proved the
formalized asymptotic assertion corresponding to Erdős problem #636.

The proof remains an explicit gap because the cited paper's argument has not
been formalized here; the definitions above nevertheless expose the actual
graph-theoretic objects and the precise interpretation of the asymptotic
notation. -/
theorem kwan_sudakov_636 : Question636 := by
  sorry Erdos636
