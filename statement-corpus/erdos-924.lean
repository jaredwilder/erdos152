/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 2$ and $l\geq 3$. Is there a graph $G$ which contains no $K_{l+1}$ such that every $k$-colouring of the edges of $G$ contains a monochromatic copy of $K_l$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#924 : [Er69b] [Er75b] graph theory | ramsey theory A question of Erdős and Hajnal. Folkman [Fo70] proved this when $k=2$. The case for general $k$ was proved by Nešetřil and Rödl [NeRo76] . See [582] for a special case and [966] for an arithmetic analogue. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #924, https://www.erdosproblems.com/924, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



-- @category research solved







import Mathlib
open Classical Filter

namespace Erdos924

/-- A finite clique of size `r` in a simple graph on `Fin n`. -/
def ContainsClique (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∃ v : Fin r → Fin n,
    Function.Injective v ∧
      ∀ i j, i ≠ j → G.Adj (v i) (v j)

/-- POSITIVE WITNESS: the complete graph on three vertices contains a triangle. -/
theorem containsClique_witness_pos :
    ContainsClique (⊤ : SimpleGraph (Fin 3)) 3 := by
  decide

/-- NEGATIVE WITNESS: deleting exactly one edge from the complete graph destroys its triangle. -/
def nearGraph : SimpleGraph (Fin 3) where
  Adj a b :=
    a ≠ b ∧
      (a ≠ 0 ∨ b ≠ 1) ∧
      (a ≠ 1 ∨ b ≠ 0)
  symm := by
    intro a b h
    exact ⟨Ne.symm h.1, Or.symm h.2.2, Or.symm h.2.1⟩
  loopless := by
    intro a h
    exact h.1 rfl

/-- NEGATIVE WITNESS: the near-miss graph has no triangle. -/
theorem containsClique_witness_neg :
    ¬ ContainsClique nearGraph 3 := by
  decide

/-- The graph has no clique of the indicated forbidden size. -/
def NoClique (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ¬ ContainsClique G r

/-- POSITIVE WITNESS: a graph on three vertices has no clique of size four. -/
theorem noClique_witness_pos :
    NoClique (⊤ : SimpleGraph (Fin 3)) 4 := by
  decide

/-- NEGATIVE WITNESS: the complete graph on three vertices does contain a triangle. -/
theorem noClique_witness_neg :
    ¬ NoClique (⊤ : SimpleGraph (Fin 3)) 3 := by
  decide

/-- 
Folkman's theorem in the general finite form recorded by the source.

A colouring is represented by a function on ordered pairs of vertices, together
with the requirement that it gives the same colour in both orientations on
every edge.  A monochromatic `K_l` is represented by an injective map from
`Fin l` whose distinct pairs are edges of one common colour.

SOURCE MAPPING:
the source asks for a graph with no `K_{l+1}` such that every `k`-colouring
of its edges contains a monochromatic `K_l`; the statement below follows those
terms in exactly that order.  The resolution node records that this is known
for general `k` by Nešetřil and Rödl [NeRo76].  The proof of that literature
theorem is not reproduced here.
-/
theorem folkman_general :
    ∀ k l : ℕ, 2 ≤ k → 3 ≤ l →
      ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        NoClique G (l + 1) ∧
          ∀ c : Fin n → Fin n → Fin k,
            (∀ u v, G.Adj u v → c u v = c v u) →
              ∃ v : Fin l → Fin n,
                Function.Injective v ∧
                  ∃ colour : Fin k,
                    ∀ i j, i ≠ j →
                      G.Adj (v i) (v j) ∧
                      c (v i) (v j) = colour := by
  sorry Erdos924
