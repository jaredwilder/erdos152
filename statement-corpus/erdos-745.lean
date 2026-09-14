/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Describe the size of the second largest component of the random graph on $n$ vertices, where each edge is included independently with probability $1/n$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#745 : [Er81] graph theory Erdős believed that almost surely the second largest component has size $\ll \log n$. This is true, as proved by Komlós, Sulyok, and Szemerédi [KSS80] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #745, https://www.erdosproblems.com/745, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter
open scoped BigOperators

-- @category research solved






open Classical Filter

namespace Erdos745

/-- The vertex set of the Erdős–Rényi random graph with `n` vertices. -/
abbrev Vertex (n : ℕ) := Fin n

/-- The number of possible edges on `n` labelled vertices. -/
def possibleEdges (n : ℕ) : ℕ :=
  n * (n - 1) / 2

/-- The number of edges of a finite simple graph, counted by ordered pairs
with the smaller endpoint first. -/
noncomputable def edgeCount {n : ℕ} (G : SimpleGraph (Vertex n)) : ℕ :=
  (Finset.univ.filter (fun e : Vertex n × Vertex n =>
    e.1 < e.2 ∧ G.Adj e.1 e.2)).card

/-- The vertex set of the connected component containing `v`, expressed using
the genuine graph-theoretic reachability relation. -/
def component {n : ℕ} (G : SimpleGraph (Vertex n)) (v : Vertex n) : Set (Vertex n) :=
  {w | G.Reachable v w}

/-- The cardinality of the connected component containing `v`. -/
noncomputable def componentSize {n : ℕ} (G : SimpleGraph (Vertex n)) (v : Vertex n) : ℕ :=
  Set.ncard (component G v)

/-- The second largest component size.  A component is eligible precisely when
there is a disjoint component at least as large; taking the maximum over all
vertices therefore gives the second order statistic, with value zero for a
graph having fewer than two components. -/
noncomputable def secondLargestComponentSize {n : ℕ}
    (G : SimpleGraph (Vertex n)) : ℕ :=
  (Finset.univ.sup fun v =>
    if ∃ u, Disjoint (component G u) (component G v) ∧
        componentSize G v ≤ componentSize G u then
      componentSize G v
    else
      0)

/-- The weight of a graph in the finite probability model in which each edge
is independently present with probability `1 / n`.  The expression is only
used asymptotically for positive `n`; the definition is total because Lean's
inverse on `ℝ` is total. -/
noncomputable def gnpWeight (n : ℕ) (G : SimpleGraph (Vertex n)) : ℝ :=
  ((n : ℝ)⁻¹) ^ edgeCount G *
    (1 - (n : ℝ)⁻¹) ^ (possibleEdges n - edgeCount G)

/-- The probability of an event in the finite labelled `G(n,1/n)` model,
obtained by summing the independent-edge weights and normalising. -/
noncomputable def gnpProbability (n : ℕ)
    (E : Finset (SimpleGraph (Vertex n))) : ℝ :=
  (E.sum (fun G => gnpWeight n G)) /
    (Finset.univ.sum (fun G : SimpleGraph (Vertex n) => gnpWeight n G))

/-- The event that the second largest component is at most a constant multiple
of `log n`.  The use of `Finset.univ` makes the event a concrete finite event
in the labelled random graph model. -/
noncomputable def logarithmicSecondComponentEvent (C : ℝ) (n : ℕ) :
    Finset (SimpleGraph (Vertex n)) :=
  Finset.univ.filter (fun G =>
    (secondLargestComponentSize G : ℝ) ≤ C * Real.log (n : ℝ))

/-- A proved sanity control for the edge-count definition: the empty graph has
no edges.  This exercises the file's graph encoding rather than being an
unrelated arithmetic example. -/
theorem edgeCount_empty_control (n : ℕ) :
    edgeCount (⊥ : SimpleGraph (Vertex n)) = 0 := by
  simp [edgeCount]

/-- The formalized content of Erdős Problem #745.  We read “almost surely” in
the standard finite-model asymptotic sense: for some constant `C`, the
probability of the event that the second largest component has size at most
`C log n` tends to one as `n` tends to infinity.  This is the settled KSS80
interpretation of the source's assertion, not an unresolved conjecture. -/
def Erdos745Claim : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Tendsto
      (fun n =>
        if n = 0 then
          0
        else
          gnpProbability n (logarithmicSecondComponentEvent C n))
      atTop (𝓝 1)

/-- The Komlós–Sulyok–Szemerédi result recorded in the resolution of the
source problem.  The source records this theorem as true; a complete proof of
the asymptotic random-graph estimate remains to be formalized here.

Source-to-statement mapping: “the second largest component” is represented by
`secondLargestComponentSize`; “random graph on `n` vertices, where each edge is
included independently with probability `1/n`” is represented by the explicit
`gnpWeight` and `gnpProbability`; and “has size << log n almost surely” is
represented by convergence to probability one of a bound by `C * log n`. -/
theorem kss80_second_largest_component :
    Erdos745Claim := by
  sorry Erdos745
