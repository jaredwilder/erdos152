/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
For any $g\geq 2$, if $n$ is sufficiently large and $\equiv 1,3\pmod{6}$ then there exists a 3-uniform hypergraph on $n$ vertices such that every pair of vertices is contained in exactly one edge (i.e. the graph is a Steiner triple system) and for any $2\leq j\leq g$ any collection of $j$ edges contains at least $j+3$ vertices.

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#207 : [Er76] combinatorics | hypergraphs Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #207, https://www.erdosproblems.com/207, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos207

/-- A finite 3-uniform hypergraph on the vertex set `Fin n`, represented by its
finite set of edges. -/
def ThreeUniformHypergraph (n : ℕ) :=
  Finset (Finset (Fin n))

/-- `IsSteinerTripleSystem n E` says that every edge of `E` has three vertices
and every pair of vertices lies in exactly one edge. -/
def IsSteinerTripleSystem (n : ℕ) (E : ThreeUniformHypergraph n) : Prop :=
  (∀ e ∈ E, e.card = 3) ∧
    (∀ p : Finset (Fin n), p.card = 2 →
      ∃! e, e ∈ E ∧ p ⊆ e)

/-- `HasExpansion g E` says that every collection of between two and `g` edges
contains at least three more vertices than edges. -/
def HasExpansion (g : ℕ) {n : ℕ} (E : ThreeUniformHypergraph n) : Prop :=
  ∀ C : Finset (Finset (Fin n)),
    C ⊆ E →
      ∀ j : ℕ, 2 ≤ j → j ≤ g → C.card = j →
        j + 3 ≤ (C.biUnion (fun e => e)).card

/-- The formal version of the existence statement in Erdos problem #207.

The source clause reads: for every `g ≥ 2`, all sufficiently large `n`
with `n ≡ 1, 3 (mod 6)` admit a 3-uniform hypergraph satisfying the Steiner
triple system condition and the expansion condition. The source records this
result as proved by Kwan, Sah, Sawhney, and Simkin; the formal derivation from
that literature result remains to be supplied here. -/
theorem erdos_207 :
    ∀ g : ℕ, 2 ≤ g →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (n % 6 = 1 ∨ n % 6 = 3) →
          ∃ E : ThreeUniformHypergraph n,
            IsSteinerTripleSystem n E ∧ HasExpansion g E := by
  sorry

/-- A proved sanity control: on one vertex, the empty hypergraph satisfies the
literal finite definitions, since there are no two-element vertex sets and no
collections of at least two edges. This is only an anti-vacuity check for the
definitions, not the asymptotic theorem. -/
theorem singleton_control :
    IsSteinerTripleSystem 1 (∅ : ThreeUniformHypergraph 1) ∧
      HasExpansion 2 (∅ : ThreeUniformHypergraph 1) := by
  constructor
  · unfold IsSteinerTripleSystem
    constructor
    · intro e he
      simp at he
    · intro p hp
      have hle : p.card ≤ (Finset.univ : Finset (Fin 1)).card :=
        Finset.card_le_univ p
      simp at hle
      omega
  · unfold HasExpansion
    intro C hC j hj hjg hcard
    have hEmpty : C = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro e he
      have he' : e ∈ (∅ : ThreeUniformHypergraph 1) := hC he
      simpa using he'
    subst C
    simp at hcard
    omega

end Erdos207
