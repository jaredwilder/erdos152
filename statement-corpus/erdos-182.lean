/-
# Erdős problem 182 — the Erdős–Sauer problem on regular subgraphs

SOURCE (frozen), `entry-graph-erdos-182.json`.

QUESTION node (`n000-question`):
  "Let $k\geq 3$. What is the maximum number of edges that a graph on $n$ vertices can contain
   if it does not have a $k$-regular subgraph? Is it $\ll n^{1+o(1)}$?"

RESOLUTION node (`n001-resolution`):
  "Asked by Erdős and Sauer. The prize of $100 is offered in [Er78] for the case $k=3$ (perhaps
   just for settling whether the answer is $\ll n$ or not). Resolved by Janzer and Sudakov
   [JaSu23], who proved that there exists some $C=C(k)>0$ such that any graph on $n$ vertices
   with at least $Cn\log\log n$ edges contains a $k$-regular subgraph. Chakraborti, Janzer,
   Methuku, and Montgomery [CJMM24b] have shown that one can take $C(k)\ll k^2$, which is the
   best possible up to an absolute constant. A construction due to Pyber, Rödl, and Szemerédi
   [PRS95] shows that this is best possible. ..."

What is formalized here is the RESOLUTION, not the question.

--------------------------------------------------------------------------------------------
CONVENTIONS NAMED (the source leaves all of these unstated)
--------------------------------------------------------------------------------------------

(1) "SUBGRAPH" = NOT SPANNING.  `SimpleGraph.Subgraph G` is a vertex subset `verts` together
    with an adjacency relation contained in `G.Adj` and supported on `verts`.  We require
    `k`-regularity only *at the vertices of the subgraph*.  Defence: the theorem is FALSE for
    spanning subgraphs — take `G` = (a huge dense graph) ⊔ (one isolated vertex); no spanning
    subgraph of `G` can be `k`-regular for `k ≥ 3`, yet `G` has as many edges as we like.  The
    subgraph in Janzer–Sudakov is obtained inside a small dense piece and is emphatically not
    spanning.

(2) NONEMPTINESS IS PART OF THE CONCLUSION.  Without `H.verts.Nonempty`, the bottom subgraph
    `⊥` (empty vertex set) satisfies "every vertex has degree `k`" vacuously and the theorem
    would be a triviality.  This is the single most important guard in the file.

(3) DEGREE IS COUNTED *INSIDE* THE SUBGRAPH, at vertices of the subgraph.  We use
    `(H.neighborSet v).ncard`, and `H.neighborSet v ⊆ H.verts` by
    `SimpleGraph.Subgraph.neighborSet_subset_verts`, so this really is the internal degree.

(4) EDGE COUNT is `G.edgeSet.ncard` (`Set.ncard`), not `G.edgeFinset.card`, purely to avoid
    carrying a `DecidableRel G.Adj` / `Fintype G.edgeSet` instance through a statement where
    `G` is universally quantified.  On a `Fintype` vertex type the two agree.

(5) "AT LEAST `C n log log n` EDGES" is read over `ℝ`, with `Real.log (Real.log n)`, and the
    claim is guarded by a threshold `N` ("for all sufficiently large `n`").  A guard is
    MANDATORY, not cosmetic: `Real.log (Real.log n) < 0` for `n ∈ {2,…,15}` and `= 0` at
    `n ∈ {0,1}`, so without a threshold the hypothesis becomes vacuous at small `n` and the
    statement is outright FALSE (the edgeless graph on 4 vertices would have to contain a
    3-regular subgraph).  `N` is existentially quantified alongside `C`, i.e. it may depend
    on `k`, matching "for `n` large in terms of `k`".

(6) BINDER ORDER.  `k` is outermost; `C` and `N` are chosen after `k` (so `C = C(k)`, exactly
    as the source writes); the graph, its vertex type and `n` come last.  This is the strong
    reading: one constant works for *all* large `n` and *all* `n`-vertex graphs.

(7) VERTEX TYPE is universally quantified (`∀ V : Type u, [Fintype V], Fintype.card V = n`)
    rather than fixed to `Fin n`.  For the positive results this is the stronger-looking
    (in fact equivalent, by transport along an equivalence) form.  For the negative result
    (Theorem 3) the quantifier flips, so there we exhibit the construction concretely on
    `Fin n` — again the stronger of the two equivalent forms.

--------------------------------------------------------------------------------------------
MATHLIB TRAPS FOUND AND AVOIDED
--------------------------------------------------------------------------------------------

TRAP A (fatal, would have wrecked the file).  `SimpleGraph.IsSubgraph x y : Prop`, i.e. the
  `≤` on `SimpleGraph V`, is a SPANNING notion — same vertex type, fewer edges.  Combining it
  with `SimpleGraph.IsRegularOfDegree` (`H ≤ G ∧ H.IsRegularOfDegree k`) reads as "`G` has a
  spanning `k`-regular subgraph", which is a different and FALSE statement (see (1)).
  `SimpleGraph.Subgraph` is the right object; `SimpleGraph.IsSubgraph` is the near-miss.

TRAP B.  `SimpleGraph.Subgraph.degree H v` is defined for EVERY `v : V`, and
  `SimpleGraph.Subgraph.degree_of_notMem_verts` gives `H.degree v = 0` for `v ∉ H.verts`.
  Hence `∀ v : V, H.degree v = k` with `k ≥ 3` silently forces `H.verts = Set.univ`, i.e.
  smuggles spanning back in through the degree side.  The membership guard `∀ v ∈ H.verts` is
  therefore load-bearing.

TRAP C.  Mathlib has NO `SimpleGraph.Subgraph.IsRegularOfDegree`; `IsRegularOfDegree` exists
  only for `SimpleGraph` and needs `[LocallyFinite G]`.  The natural-looking
  `H.coe.IsRegularOfDegree k` is faithful but drags `Fintype (H.coe.neighborSet v)` instances
  through an existential over `H`.  We state regularity directly on `neighborSet` instead;
  `SimpleGraph.Subgraph.coe_degree` is the bridge showing these agree.

TRAP D.  `Real.log (Real.log n)` is *not* `logb`-style undefined below `e^e`; Mathlib's
  `Real.log` is junk-valued (`Real.log x = 0` for `x ≤ 0`), so a bad statement compiles happily
  and is false.  Handled by the threshold `N` in (5).
-/

-- @category research solved
-- @AMS 5
-- Category vocabulary and AMS tagging adopted from the
-- formal-conjectures corpus (509 files, measured 2026-08-28). Written as a comment
-- rather than the corpus attribute form, so this artifact still elaborates
-- standalone, outside their project.





import Mathlib
namespace Erdos182

open SimpleGraph

universe u

/-- `H` is a (nonempty) `k`-regular subgraph of `G`: `H` has at least one vertex, and every
vertex of `H` has exactly `k` neighbours *within* `H`.

`H` is **not** required to be spanning (`H.verts` may be a proper subset of the vertex type),
nor induced.  See convention (1)–(3) in the header. -/
def IsKRegularSubgraph {V : Type u} {G : SimpleGraph V} (H : G.Subgraph) (k : ℕ) : Prop :=
  H.verts.Nonempty ∧ ∀ v ∈ H.verts, (H.neighborSet v).ncard = k

/-! ### Theorem 1 (MAIN — the resolution) -/

/-- **Erdős–Sauer problem, resolved by Janzer and Sudakov (2023).**

For every `k ≥ 3` there is a constant `C = C(k) > 0` such that every graph on `n` vertices with
at least `C · n · log log n` edges contains a `k`-regular subgraph, for all sufficiently large
`n`.

Binder order: `k`, then `C` and the largeness threshold `N` (both may depend on `k`), then
`n ≥ N`, then the vertex type and the graph. -/
theorem janzer_sudakov_regular_subgraph (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V : Type u) [Fintype V], Fintype.card V = n →
        ∀ G : SimpleGraph V,
          C * (n : ℝ) * Real.log (Real.log n) ≤ (G.edgeSet.ncard : ℝ) →
            ∃ H : G.Subgraph, IsKRegularSubgraph H k := by
  sorry

/-! ### Theorem 2 (SHARPENING — stated separately, deliberately NOT merged into Theorem 1) -/

/-- **Chakraborti, Janzer, Methuku and Montgomery (2024): one can take `C(k) ≪ k²`.**

The point of the sharpening is that a *single absolute* constant `A`, independent of `k`,
works with the profile `A · k² `.  Hence `A` is bound OUTSIDE `k`, which is exactly what
distinguishes this from Theorem 1; the largeness threshold `N` is still allowed to depend
on `k`.

Note this does not formally imply Theorem 1 only because of that binder difference — with `k`
fixed, `C := A * k^2` recovers it. -/
theorem chakraborti_janzer_methuku_montgomery_k_squared :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (V : Type u) [Fintype V], Fintype.card V = n →
        ∀ G : SimpleGraph V,
          A * (k : ℝ) ^ 2 * (n : ℝ) * Real.log (Real.log n) ≤ (G.edgeSet.ncard : ℝ) →
            ∃ H : G.Subgraph, IsKRegularSubgraph H k := by
  sorry

/-! ### Theorem 3 (OPTIMALITY — the matching construction; also separate) -/

/-- **Pyber–Rödl–Szemerédi construction, and the matching `k²` lower bound.**

"A construction due to Pyber, Rödl and Szemerédi shows that this is best possible", combined
with "`C(k) ≪ k²` … is the best possible up to an absolute constant": there is an absolute
`c > 0` such that for every `k ≥ 3` there are arbitrarily large `n` and `n`-vertex graphs with
at least `c · k² · n · log log n` edges and **no** `k`-regular subgraph.

Stated on `Fin n`, i.e. the construction is exhibited concretely (stronger than merely
asserting some finite vertex type exists). -/
theorem pyber_rodl_szemeredi_optimality :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 3 ≤ k → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ G : SimpleGraph (Fin n),
        c * (k : ℝ) ^ 2 * (n : ℝ) * Real.log (Real.log n) ≤ (G.edgeSet.ncard : ℝ) ∧
        ∀ H : G.Subgraph, ¬ IsKRegularSubgraph H k := by
  sorry

/-! ### Sanity lemmas: the definition really says what the header claims. -/

/-- The neighbours counted by `IsKRegularSubgraph` all lie inside the subgraph. -/
example {V : Type u} {G : SimpleGraph V} (H : G.Subgraph) (v : V) :
    H.neighborSet v ⊆ H.verts :=
  H.neighborSet_subset_verts v

/-- TRAP B, made explicit: outside `H.verts` the subgraph degree is `0`, so demanding
`k`-regularity at *every* vertex of the ambient type would force `H` to be spanning. -/
example {V : Type u} {G : SimpleGraph V} (H : G.Subgraph) (v : V) (hv : v ∉ H.verts) :
    H.neighborSet v = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false, SimpleGraph.Subgraph.mem_neighborSet]
  exact fun h => hv (H.edge_vert h)

end Erdos182

-- ⛔ FOOTPRINTS, PRINTED ON EVERY COMPILE, NOT RECORDED ONCE.
-- Clean is [propext, Classical.choice, Quot.sound]. `sorryAx` means the theorem is NOT
-- PROVED, and seeing it here is the point: no reader and no later session can mistake a
-- partial artifact for a proof. A line flips on its own when its last `sorry` closes.
#print axioms Erdos182.janzer_sudakov_regular_subgraph
#print axioms Erdos182.chakraborti_janzer_methuku_montgomery_k_squared
#print axioms Erdos182.pyber_rodl_szemeredi_optimality
