/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Does every graph with $n$ vertices and $2n-2$ edges contain a cycle and another vertex adjacent to three vertices on the cycle?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#916 : [Er67b] graph theory | cycles This would be a stronger form of the result of Dirac [Di60] that every such graph contains a subgraph homeomorphic to $K_4$. The answer is yes, as proved by Thomassen [Th74] . Additional thanks to : Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #916, https://www.erdosproblems.com/916, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None formalisable JoshuaB Working on formalising parabamoghv Previous Next
-/



import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos916

/-- `HasCycleTriple G` means that `G` contains a simple cycle of length at least
three and a vertex outside that cycle adjacent to three vertices on it. -/
def HasCycleTriple {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ k : Fin (n + 1), ∃ hk : 3 ≤ k.val,
    ∃ f : Fin k.val → Fin n, ∃ x : Fin n,
      Function.Injective f ∧
        x ∉ Set.range f ∧
        (let hkpos : 0 < k.val := by omega
         let next : ∀ i : Fin k.val, Fin k.val :=
           fun i => ⟨(i.val + 1) % k.val, Nat.mod_lt _ hkpos⟩
         (∀ i : Fin k.val, G.Adj (f i) (f (next i))) ∧
         G.Adj x (f ⟨0, by omega⟩) ∧
         G.Adj x (f ⟨1, by omega⟩) ∧
         G.Adj x (f ⟨2, by omega⟩))

/-- POSITIVE WITNESS: the complete graph on four vertices has a triangle and
a fourth vertex adjacent to all three vertices of that triangle. -/
theorem HasCycleTriple_witness_pos :
    HasCycleTriple (⊤ : SimpleGraph (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: the complete graph on four vertices with exactly the edge
between vertices `2` and `3` removed is a near miss, failing only the required
adjacency from the outside vertex to the third cycle vertex. -/
def missingEdgeGraph : SimpleGraph (Fin 4) where
  Adj i j :=
    i ≠ j ∧
      ¬ ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2))
  symm := by
    intro i j hij
    rcases hij with ⟨hne, hmiss⟩
    constructor
    · exact Ne.symm hne
    · intro h
      apply hmiss
      rcases h with h | h
      · exact Or.inr ⟨h.2, h.1⟩
      · exact Or.inl ⟨h.2, h.1⟩
  loopless := by
    intro i
    simp

/-- NEGATIVE WITNESS: removing one edge from the positive four-vertex example
destroys the required cycle-and-outside-vertex configuration. -/
theorem HasCycleTriple_witness_neg :
    ¬ HasCycleTriple (missingEdgeGraph : SimpleGraph (Fin 4)) := by
  decide

/-- Every simple graph on `n` vertices with exactly `2 * n - 2` edges contains
a cycle and another vertex adjacent to three vertices on that cycle.

The source sentence reads directly as follows: the graph has `n` vertices and
`2n-2` edges, and the conclusion is the configuration represented by
`HasCycleTriple`; no reversal of a nonsymmetric relation is involved here.
The result is recorded by the source as proved by Thomassen [Th74]. -/
theorem erdos_916 :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card = 2 * n - 2 →
        HasCycleTriple G := by
  sorry Erdos916
