/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Suppose $n\geq kr+(t-1)(k-1)$ and the edges of the complete $r$-uniform hypergraph on $n$ vertices are $t$-coloured. Prove that some colour class must contain $k$ pairwise disjoint edges.

NODE n001-resolution (resolution), VERBATIM:
#780 : [Er76] combinatorics | hypergraphs | chromatic number In other words, this problem asks to determine the chromatic number of the Kneser graph. This would be best possible: if $n=kr-1+(t-1)(k-1)$ then decomposing $[n]$ as one set $X_1$ of size $kr-1$ and $t-1$ sets $X_2,\ldots,X_{t}$ of size $k-1$, a colouring without $k$ pairwise disjoint edges is given colouring all subsets of $X_0$ in colour $1$ and assigning an edge with colour $2\leq i\leq t$ if $i$ is minimal such that $X_i$ intersects the edge. When $k=2$ this was conjectured by Kneser and proved by Lovász [Lo78] . The general case was proved by Alon, Frankl, and Lovász [AFL86] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos780

/-- An edge of the complete `r`-uniform hypergraph on `n` vertices, represented as
a finite subset of `Fin n` having cardinality `r`. -/
def UniformEdge (n r : ℕ) := {e : Finset (Fin n) // e.card = r}

/-- A `t`-colouring of the edges of the complete `r`-uniform hypergraph on `n`
vertices. -/
def EdgeColoring (n r t : ℕ) := UniformEdge n r → Fin t

/-- A family of `k` uniform edges is pairwise disjoint. -/
def PairwiseDisjointEdges (n r k : ℕ) (F : Fin k → UniformEdge n r) : Prop :=
  ∀ ⦃i j : Fin k⦄, i ≠ j → Disjoint (F i).1 (F j).1

/-- The assertion that a colouring has a colour class containing `k` pairwise
disjoint edges. -/
def HasMonochromaticPacking (n r t k : ℕ) (c : EdgeColoring n r t) : Prop :=
  ∃ colour : Fin t, ∃ F : Fin k → UniformEdge n r,
    (∀ i, c (F i) = colour) ∧ PairwiseDisjointEdges n r k F

/-- A kernel-checked control showing that the definitions describe an actual
nonempty monochromatic packing in the one-vertex, one-edge, one-colour case. -/
theorem control_one_edge :
    HasMonochromaticPacking 1 1 1 1 (fun _ => 0) := by
  refine ⟨0, (fun _ => ⟨{0}, by simp⟩), ?_, ?_⟩
  · intro i
    rfl
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

/-- The Erdős problem #780, formalized using `UniformEdge` for the edges of the
complete uniform hypergraph.

The source says: if `n ≥ k*r + (t-1)*(k-1)`, every `t`-colouring has a colour
class containing `k` pairwise disjoint edges. The parameters are required to be
positive, as is implicit in the phrase `t`-coloured and in the existence of
`k`-edge packings. The combinatorial theorem is known by the resolution node;
the proof remains to be supplied here. -/
theorem erdos_780
    {n r t k : ℕ}
    (hr : 1 ≤ r)
    (ht : 1 ≤ t)
    (hk : 1 ≤ k)
    (hn : k * r + (t - 1) * (k - 1) ≤ n)
    (colouring : EdgeColoring n r t) :
    HasMonochromaticPacking n r t k colouring := by
  sorry Erdos780
