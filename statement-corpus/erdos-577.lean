/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $G$ is a graph with $4k$ vertices and minimum degree at least $2k$ then $G$ contains $k$ vertex-disjoint $4$-cycles.

NODE n001-resolution (resolution), VERBATIM:
#577 : [Er90c] graph theory A conjecture of Erdős and Faudree. Proved by Wang [Wa10] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #577, https://www.erdosproblems.com/577, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/



-- @category research solved

import Mathlib
open Classical







open Classical Filter

namespace Erdos577

/-- A four-cycle in a simple graph, represented by an injective cyclic listing of
its four vertices. Chords are allowed, as they are irrelevant to containing a
copy of a 4-cycle. -/
def FourCycle {V : Type*} (G : SimpleGraph V) (q : Fin 4 → V) : Prop :=
  Function.Injective q ∧
    G.Adj (q 0) (q 1) ∧
    G.Adj (q 1) (q 2) ∧
    G.Adj (q 2) (q 3) ∧
    G.Adj (q 3) (q 0)

/-- `DisjointCycles G k` means that `G` contains `k` four-cycles whose vertex
sets are pairwise disjoint. -/
def DisjointCycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ q : Fin k → Fin 4 → V,
    (∀ i, FourCycle G (q i)) ∧
    (∀ i j : Fin k, i ≠ j → ∀ a b : Fin 4, q i a ≠ q j b)

/-- The complete graph on four vertices contains the explicitly listed
four-cycle. This is a proved control exercising the cycle definition. -/
theorem complete_four_cycle :
    FourCycle (⊤ : SimpleGraph (Fin 4)) (fun x : Fin 4 => x) := by
  refine ⟨Function.injective_id, ?_⟩
  simp

/-- The complete graph on four vertices contains one vertex-disjoint
four-cycle. This is a non-vacuous proved control for `DisjointCycles`. -/
theorem complete_one_cycle :
    DisjointCycles (⊤ : SimpleGraph (Fin 4)) 1 := by
  let q : Fin 1 → Fin 4 → Fin 4 := fun _ x => x
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa [q] using complete_four_cycle
  · intro i j hij a b
    have h : i = j := Subsingleton.elim _ _
    exact (hij h).elim

/-- Formalization of Erdős Problem #577.

The source says: a graph `G` with `4k` vertices and minimum degree at least
`2k` contains `k` vertex-disjoint 4-cycles. Here the subject is a genuine
finite simple graph `G : SimpleGraph V`, with finiteness represented by
`[Fintype V]`; `G.degree v` expresses the degree condition, and
`DisjointCycles G k` expresses the conclusion.

The resolution node records that this result was proved by Wang [Wa10].
The proof of the resulting theorem is not reconstructed here and remains an
honest gap. -/
theorem erdos_577 {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v : V, 2 * k ≤ G.degree v) :
    DisjointCycles G k := by
  sorry

#print axioms complete_four_cycle
#print axioms complete_one_cycle
#print axioms erdos_577

end Erdos577
