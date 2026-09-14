/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Does there exist a $3$-critical $3$-uniform hypergraph in which every vertex has degree $\geq 7$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#834 : [Er74d,p.282] graph theory | hypergraphs A problem of Erdős and Lovász. They do not specify what is meant by $3$-critical. One definition in the literature is: a hypergraph is $3$-critical if there is a set of $3$ vertices which intersects every edge, but no such set of size $2$, and yet for any edge $e$ there is a pair of vertices which intersects every edge except $e$. Raphael Steiner observes that a $3$-critical hypergraph in this sense has bounded size, so this problem would be a finite computation, and perhaps is not what they meant. An alternative definition is that a hypergraph is $3$-critical if it has chromatic number $3$, but its chromatic number becomes $2$ after deleting any edge or vertex. In either case, this has been resolved by Li [Li25] . In the first formulation, the transversal notion of criticality, Li proves that a $3$-critical $3$-uniform hypergraph must have a vertex of degree $\leq 6$. On the other hand, in the second formulation, Li provides an explicit $3$-critical $3$-uniform hypergraph on $9$ vertices with minimum degree $7$. Additional thanks to : Alfaiz and Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (2) Proof claims (0) More information and links This page was last edited 01 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #834, https://www.erdosproblems.com/834, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes ruiliangli Open to collaboration None Currently working on ruiliangli Looks difficult None Looks tractable ruiliangli Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos834

/-- A finite hypergraph whose vertices are `Fin n`. -/
structure Hypergraph (n : ℕ) where
  edges : Finset (Finset (Fin n))

/-- The predicate that every edge of a hypergraph has exactly three vertices. -/
def IsThreeUniform {n : ℕ} (H : Hypergraph n) : Prop :=
  ∀ e ∈ H.edges, e.card = 3

/-- The three pairwise disjoint triples used for the transversal-critical witness. -/
def hDisjoint : Hypergraph 9 where
  edges :=
    ({({0, 1, 2} : Finset (Fin 9)),
      ({3, 4, 5} : Finset (Fin 9)),
      ({6, 7, 8} : Finset (Fin 9))} : Finset (Finset (Fin 9)))

/-- A near-miss for `hDisjoint`, obtained by deleting exactly one edge. -/
def hDisjointNear : Hypergraph 9 where
  edges :=
    ({({0, 1, 2} : Finset (Fin 9)),
      ({3, 4, 5} : Finset (Fin 9))} : Finset (Finset (Fin 9)))

/-- The complete 3-uniform hypergraph on `Fin n`. -/
def allTriples (n : ℕ) : Hypergraph n where
  edges := Finset.univ.filter (fun e : Finset (Fin n) => e.card = 3)

/-- The complete 3-uniform hypergraph on five vertices. -/
def hK5 : Hypergraph 5 :=
  allTriples 5

/-- A near-miss for `hK5`, obtained by adjoining one isolated vertex. -/
def hK5Plus : Hypergraph 6 where
  edges :=
    (allTriples 6).edges.filter
      (fun e => ∀ x ∈ e, x.val < 5)

/-- The degree of a vertex in a finite hypergraph. -/
def degree {n : ℕ} (H : Hypergraph n) (v : Fin n) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

/-- Every vertex has degree at least seven. -/
def MinimumDegreeSeven {n : ℕ} (H : Hypergraph n) : Prop :=
  ∀ v : Fin n, 7 ≤ degree H v

/-- A set of vertices intersects every edge of a hypergraph. -/
def Hits {n : ℕ} (H : Hypergraph n) (s : Finset (Fin n)) : Prop :=
  ∀ e ∈ H.edges, (s ∩ e).Nonempty

/-- The transversal notion of 3-criticality from the source. -/
def TransversalCritical {n : ℕ} (H : Hypergraph n) : Prop :=
  (∃ s : Finset (Fin n), s.card = 3 ∧ Hits H s) ∧
    (¬ ∃ s : Finset (Fin n), s.card = 2 ∧ Hits H s) ∧
    (∀ e ∈ H.edges,
      ∃ s : Finset (Fin n), s.card = 2 ∧
        ∀ e' ∈ H.edges, e' ≠ e → (s ∩ e').Nonempty)

/-- A coloring has no monochromatic nonempty edge. -/
def ProperColoring {n k : ℕ} (H : Hypergraph n) (c : Fin n → Fin k) : Prop :=
  ∀ e ∈ H.edges, e.Nonempty →
    ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- Two-colorability of a finite hypergraph. -/
def TwoColorable {n : ℕ} (H : Hypergraph n) : Prop :=
  ∃ c : Fin n → Fin 2, ProperColoring H c

/-- Three-colorability without two-colorability. -/
def ChromaticThree {n : ℕ} (H : Hypergraph n) : Prop :=
  (∃ c : Fin n → Fin 3, ProperColoring H c) ∧ ¬ TwoColorable H

/-- The chromatic notion of 3-criticality from the source: deleting any edge
or any vertex leaves a two-colorable hypergraph. -/
def ChromaticCritical {n : ℕ} (H : Hypergraph n) : Prop :=
  ChromaticThree H ∧
    (∀ e ∈ H.edges,
      TwoColorable
        { edges := H.edges.filter (fun e' => e' ≠ e) }) ∧
    (∀ v : Fin n,
      TwoColorable
        { edges := H.edges.filter (fun e => v ∉ e) })

/-- The source leaves the meaning of `3-critical` ambiguous, so this is the
literal disjunction of its transversal and chromatic readings. -/
def Question : Prop :=
  (∃ n : ℕ, ∃ H : Hypergraph n,
    IsThreeUniform H ∧ TransversalCritical H ∧ MinimumDegreeSeven H) ∨
  (∃ n : ℕ, ∃ H : Hypergraph n,
    IsThreeUniform H ∧ ChromaticCritical H ∧ MinimumDegreeSeven H)

/-- POSITIVE WITNESS: the three disjoint edges form a 3-uniform hypergraph. -/
theorem isThreeUniform_witness_pos : IsThreeUniform hDisjoint := by
  decide

/-- NEGATIVE WITNESS: deleting one vertex from one edge makes that edge have
cardinality two, violating exactly the uniformity condition. -/
theorem isThreeUniform_witness_neg :
    ¬ IsThreeUniform
      { edges :=
        ({({0, 1} : Finset (Fin 9)),
          ({3, 4, 5} : Finset (Fin 9)),
          ({6, 7, 8} : Finset (Fin 9))} : Finset (Finset (Fin 9))) } := by
  decide

/-- POSITIVE WITNESS: the three disjoint triples are transversal-critical. -/
theorem transversalCritical_witness_pos :
    TransversalCritical hDisjoint := by
  decide

/-- NEGATIVE WITNESS: after deleting one edge, a two-element transversal
exists, so exactly the minimum-transversal condition fails. -/
theorem transversalCritical_witness_neg :
    ¬ TransversalCritical hDisjointNear := by
  decide

/-- POSITIVE WITNESS: the complete 3-uniform hypergraph on five vertices is
chromatic-critical in the edge-and-vertex deletion sense. -/
theorem chromaticCritical_witness_pos :
    ChromaticCritical hK5 := by
  decide

/-- NEGATIVE WITNESS: adjoining one isolated vertex preserves the chromatic
number but makes deletion of that vertex fail to lower it. -/
theorem chromaticCritical_witness_neg :
    ¬ ChromaticCritical hK5Plus := by
  decide

/-- POSITIVE WITNESS: the complete 3-uniform hypergraph on eight vertices has
minimum degree at least seven. -/
theorem minimumDegreeSeven_witness_pos :
    MinimumDegreeSeven (allTriples 8) := by
  decide

/-- NEGATIVE WITNESS: the empty hypergraph fails the minimum-degree condition
at every vertex. -/
theorem minimumDegreeSeven_witness_neg :
    ¬ MinimumDegreeSeven
      ({ edges := (∅ : Finset (Finset (Fin 8))) } : Hypergraph 8) := by
  decide

/-- RESOLUTION, transversal reading. The source says that every transversal-
critical 3-uniform hypergraph has a vertex of degree at most six; hence no
such hypergraph can have minimum degree at least seven. This literature result
is recorded as an explicit honest gap. -/
theorem transversal_no_high_degree :
    ¬ ∃ n : ℕ, ∃ H : Hypergraph n,
      IsThreeUniform H ∧ TransversalCritical H ∧ MinimumDegreeSeven H := by
  sorry

/-- RESOLUTION, chromatic reading. The source says that Li provides an
explicit chromatic-critical 3-uniform hypergraph on nine vertices with
minimum degree seven. The construction and its verification are recorded as
an explicit honest gap. -/
theorem chromatic_exists_high_degree :
    ∃ H : Hypergraph 9,
      IsThreeUniform H ∧ ChromaticCritical H ∧ MinimumDegreeSeven H := by
  sorry

/-- The disjunctive question is true under the chromatic interpretation and
false under the transversal interpretation. -/
theorem question_resolution : Question := by
  right
  exact ⟨9, chromatic_exists_high_degree⟩

#print axioms isThreeUniform_witness_pos
#print axioms transversalCritical_witness_pos
#print axioms chromaticCritical_witness_pos
#print axioms question_resolution

end Erdos834
