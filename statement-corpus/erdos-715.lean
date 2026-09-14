/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Does every regular graph of degree $4$ contain a regular subgraph of degree $3$? Is there any $r$ such that every regular graph of degree $r$ must contain a regular subgraph of degree $3$?

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#715 : [Er75] [Er81] graph theory A problem of Berge (or Berge and Sauer). Alon, Friedland, and Kalai [AFK84] proved that every $4$-regular graph plus an edge contains a $3$-regular subgraph, and hence in particular every $r$-regular graph with $r\geq 5$ contains a $3$-regular subgraph. The answer is yes, proved by Tashkinov [Ta82] . Additional thanks to : Zach Hunter and Hitesh Kumar Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 06 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #715, https://www.erdosproblems.com/715, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical






open Classical Filter

namespace Erdos715

-- @category research solved

/-- A graph is regular of degree `r` when every vertex has graph-theoretic degree `r`. -/
def IsRegularGraph {V : Type} [Fintype V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ v : V, G.degree v = r

/-- A genuine subgraph of `G` whose vertex set may be a proper subset, and which is
regular of the prescribed degree.  The graph carried by `graph` has as vertices
the elements of `verts`, and `sub` states that each of its edges is an edge of
the ambient graph. -/
structure RegularSubgraph {V : Type} [Fintype V] (G : SimpleGraph V) (r : ℕ) where
  verts : Set V
  graph : SimpleGraph {v : V // v ∈ verts}
  sub : ∀ ⦃u v : {x : V // x ∈ verts}⦄, graph.Adj u v → G.Adj u.1 v.1
  regular : ∀ v, graph.degree v = r

/-- The ambient graph contains a regular subgraph of degree `r`. -/
def HasRegularSubgraph {V : Type} [Fintype V] (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (RegularSubgraph G r)

/-- The first question from the source, formalized for finite simple graphs:
does every degree-four regular graph contain a degree-three regular subgraph? -/
def EveryFourRegularHasThree : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    IsRegularGraph G 4 → HasRegularSubgraph G 3

/-- The second question from the source, formalized as the existence of a degree
for which every regular finite simple graph contains a degree-three regular
subgraph. -/
def SomeRegularDegreeHasThree : Prop :=
  ∃ r : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    IsRegularGraph G r → HasRegularSubgraph G 3

/-- A proved sanity control: the complete graph on four vertices is regular of
degree three and itself supplies a degree-three regular subgraph. -/
theorem complete_four_control :
    IsRegularGraph (⊤ : SimpleGraph (Fin 4)) 3 ∧
      HasRegularSubgraph (⊤ : SimpleGraph (Fin 4)) 3 := by
  constructor
  · intro v
    simp
  · let U : Set (Fin 4) := Set.univ
    let H : SimpleGraph {v : Fin 4 // v ∈ U} := ⊤
    refine ⟨{ verts := U
              graph := H
              sub := ?_
              regular := ?_ }⟩
    · intro u v huv
      simp
    · intro v
      simp [U, H]

/-- The recorded resolution answers the existential second question affirmatively.
The formal statement is faithful to the source's claim that every regular graph
of degree at least five has a degree-three regular subgraph; the proof of that
substantive graph-theoretic theorem is not reproduced here. -/
theorem resolved_existence : SomeRegularDegreeHasThree := by
  sorry

#print axioms complete_four_control

end Erdos715
