/-
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Is it true that in any $2$-colouring of the edges of $K_n$ there must exist at least\[(1+o(1))\frac{n^2}{12}\]many edge-disjoint monochromatic triangles?

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#76 : [Er95] [Er97d] [Va99,3.54] graph theory | ramsey theory Conjectured by Erdős, Faudreee, and Ordman. This would be best possible, as witnessed by dividing the vertices of $K_n$ into two equal parts and colouring all edges between the parts red and all edges inside the parts blue. The answer is yes, proved by Gruslys and Letzter [GrLe20] . In [Er97d] Erdős also asks for a lower bound for the count of edge-disjoint monochromatic triangles in single colour (the colour chosen to maximise this quantity), and speculates that the answer is $\geq cn^2$ for some constant $c>1/24$. Additional thanks to : Julius Schmerling and Tuan Tran Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #76, https://www.erdosproblems.com/76, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A060407 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos76

/-- A symmetric two-colouring of the edges of a graph which is required to be
complete.  The graph argument is the actual `SimpleGraph`, rather than a tag
encoding a colouring. -/
def IsTwoColouring {n : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin n → Fin 2) : Prop :=
  G = ⊤ ∧ ∀ u v, c u v = c v u

/-- A three-vertex set in the complete graph. -/
def IsTriangle {n : ℕ} (T : Finset (Fin n)) : Prop :=
  T.card = 3

/-- Two vertex sets have no common edge.  Thus vertices may be shared, but no
pair of distinct vertices belongs to both sets. -/
def EdgeDisjoint {n : ℕ} (T U : Finset (Fin n)) : Prop :=
  ∀ u v, u ∈ T → v ∈ T → u ≠ v → ¬ (u ∈ U ∧ v ∈ U)

/-- All edges spanned by a vertex set have one colour. -/
def IsMonochromatic {n : ℕ} (c : Fin n → Fin n → Fin 2)
    (T : Finset (Fin n)) : Prop :=
  ∃ d : Fin 2, ∀ u v, u ∈ T → v ∈ T → u ≠ v → c u v = d

/-- There is a family of `k` pairwise edge-disjoint monochromatic triangles. -/
def HasTrianglePacking {n k : ℕ} (c : Fin n → Fin n → Fin 2) : Prop :=
  ∃ T : Fin k → Finset (Fin n),
    (∀ i, IsTriangle (T i)) ∧
    (∀ i j, i ≠ j → EdgeDisjoint (T i) (T j)) ∧
    (∀ i, IsMonochromatic c (T i))

/-- The edge-disjointness relation is symmetric.  This is a proved control
for the direction of the relation used in the packing definition. -/
theorem edgeDisjoint_symm {n : ℕ} {T U : Finset (Fin n)}
    (h : EdgeDisjoint T U) : EdgeDisjoint U T := by
  intro u v hu hv huv
  intro hT
  exact h u v hT.1 hT.2 huv ⟨hu, hv⟩

/-- Formalization of the resolved statement of Erdős Problem #76.

The source asks whether every two-colouring of the edges of `K_n` contains
at least `(1+o(1)) n^2 / 12` edge-disjoint monochromatic triangles.  Here
`(1+o(1))` is read in its standard eventual lower-bound sense: for every
positive real `ε`, all sufficiently large `n` admit a packing of size at
least `(1/12 - ε)n²`.

The theorem is recorded as settled in the source by Gruslys and Letzter
[GrLe20].  The proof of that literature result is not reproduced here; the
remaining proof obligation is therefore an explicit honest gap.

SOURCE MAPPING: “in any 2-colouring of the edges of K_n” becomes
`IsTwoColouring G c` with `G` a `SimpleGraph (Fin n)` equal to `⊤`;
“edge-disjoint monochromatic triangles” becomes `HasTrianglePacking c k`;
and “at least `(1+o(1)) n²/12`” becomes the displayed eventual
`(1/12 - ε) * n² ≤ k` bound. -/
theorem erdos_76 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (G : SimpleGraph (Fin n))
          (c : Fin n → Fin n → Fin 2),
          IsTwoColouring G c →
          ∃ k : ℕ,
            (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (k : ℝ) ∧
              HasTrianglePacking c k := by
  sorry Erdos76
