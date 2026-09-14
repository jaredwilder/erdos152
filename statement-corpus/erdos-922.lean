/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 0$. Let $G$ be a graph such that every subgraph $H$ contains an independent set of size $\geq (n-k)/2$, where $n$ is the number of vertices of $H$. Must $G$ have chromatic number at most $k+2$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#922 : [ErHa67b] [Er69b] graph theory | chromatic number A question of Erdős and Hajnal [ErHa67b] . The case $k=0$ is trivial, but they could not prove this even for $k=1$. This is true, and was proved by Folkman [Fo70b] . See also [73] . Additional thanks to : Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #922, https://www.erdosproblems.com/922, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos922

/-- `HasColoring G k` means that the vertices of `G` can be properly colored with
`k + 2` colors. -/
def HasColoring {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin (k + 2), ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

/-- POSITIVE WITNESS: the empty graph on two vertices is colorable with two colors. -/
theorem HasColoring_witness_pos :
    HasColoring (⊥ : SimpleGraph (Fin 2)) 0 := by
  decide

/-- NEGATIVE WITNESS: adding all three edges to the positive pattern makes a
three-vertex graph not colorable with two colors. -/
theorem HasColoring_witness_neg :
    ¬ HasColoring (⊤ : SimpleGraph (Fin 3)) 0 := by
  decide

/-- `UniversalLargeIndependent G k` formalizes the hypothesis that every
induced vertex-subgraph has an independent set whose doubled size is at least
`n - k`.  This is the integer form of size at least `(n-k)/2`.
Checking induced subgraphs is sufficient for the source's assertion about all
subgraphs, since deleting edges can only create more independent sets. -/
def UniversalLargeIndependent {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ U : Finset V,
    ∃ I : Finset V,
      I ⊆ U ∧
        (∀ ⦃v w : V⦄, v ∈ I → w ∈ I → v ≠ w → ¬ G.Adj v w) ∧
        2 * I.card ≥ U.card - k

/-- POSITIVE WITNESS: every induced subgraph of the empty graph on two
vertices has an independent set of the required size when `k = 0`. -/
theorem UniversalLargeIndependent_witness_pos :
    UniversalLargeIndependent (⊥ : SimpleGraph (Fin 2)) 0 := by
  decide

/-- NEGATIVE WITNESS: the complete graph on three vertices is a near miss,
obtained by adding edges to the positive graph; its full three-vertex
subgraph has no independent set of doubled size at least three. -/
theorem UniversalLargeIndependent_witness_neg :
    ¬ UniversalLargeIndependent (⊤ : SimpleGraph (Fin 3)) 0 := by
  decide

/-- The conclusion of Erdős problem #922: a graph satisfying the universal
large-independent-set hypothesis has chromatic number at most `k + 2`,
expressed by the existence of a proper coloring with that many colors. -/
theorem folkman_answer {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) :
    UniversalLargeIndependent G k → HasColoring G k := by
  sorry Erdos922
