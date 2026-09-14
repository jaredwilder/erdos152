/- 
SOURCE (frozen), NODE n000-question (question), VERBATIM:
Let $G$ be a graph with no isolated vertices and $m$ edges. Is it true that\[R(G) \leq 2^{O(m^{1/2})}?\]

NODE n001-resolution (resolution), VERBATIM:
#546 : [Er84b,p.10] graph theory | ramsey theory This is true, and was proved by Sudakov [Su11] . The analogous question for $\geq 3$ colours is still open. Alon, Krivelevich, and Sudakov [AKS03] had earlier given a short proof of this when $G$ is bipartite. A more precise question is [545] . This problem is #11 in Ramsey Theory in the graphs problem collection. Additional thanks to : Zach Hunter and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 18 November 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #546, https://www.erdosproblems.com/546, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos546

/-- A finite graph on `Fin n` has no isolated vertices when every vertex has a neighbour. -/
def HasNoIsolatedVertices (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, ∃ w, G.Adj v w

/-- The number of edges of a graph on `Fin n`, counting each unordered edge once
by retaining the ordered pairs whose first endpoint is smaller. -/
def edgeCount (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter
    (fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2)).card

/-- A two-colouring of the pairs of vertices of `Fin N`, represented by a symmetric
Boolean-valued function. -/
def IsSymmetricColouring (N : ℕ) (c : Fin N → Fin N → Bool) : Prop :=
  ∀ u v, c u v = c v u

/-- The graph `G` has a monochromatic copy in the colouring `c` when some injective
map from its vertices into `Fin N` sends every edge of `G` to one colour. -/
def HasMonochromaticCopy (n N : ℕ) (G : SimpleGraph (Fin n))
    (c : Fin N → Fin N → Bool) : Prop :=
  ∃ f : Fin n → Fin N, Function.Injective f ∧
    ∃ b : Bool, ∀ u v, G.Adj u v → c (f u) (f v) = b

/-- `RamseyProperty G N` means that every symmetric two-colouring of the pairs of
`Fin N` contains a monochromatic copy of `G`. -/
def RamseyProperty (n : ℕ) (G : SimpleGraph (Fin n)) (N : ℕ) : Prop :=
  ∀ c : Fin N → Fin N → Bool, IsSymmetricColouring N c →
    HasMonochromaticCopy n N G c

/-- The Ramsey number of `G`, defined as the infimum of the set of orders having
the Ramsey property. The nonemptiness control below is required because `Nat.sInf`
returns the default value on an empty set. -/
noncomputable def RamseyNumber (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {N : ℕ | RamseyProperty n G N}

/-- The finite Ramsey theorem supplies at least one order having the Ramsey property.
This is recorded as an explicit assumed literature input; its proof is not developed here. -/
theorem ramseySet_nonempty (n : ℕ) (G : SimpleGraph (Fin n)) :
    Set.Nonempty {N : ℕ | RamseyProperty n G N} := by
  sorry

/-- The set used in `RamseyNumber` is bounded below by zero, so its infimum is not
using an unbounded-below default. -/
theorem ramseySet_bddBelow (n : ℕ) (G : SimpleGraph (Fin n)) :
    Set.BddBelow {N : ℕ | RamseyProperty n G N} := by
  refine ⟨0, ?_⟩
  intro N hN
  exact Nat.zero_le N

/-- A proved sanity control: the empty graph on the empty vertex type has the
Ramsey property at order zero. -/
theorem emptyGraph_ramseyProperty :
    RamseyProperty 0 (⊥ : SimpleGraph (Fin 0)) 0 := by
  intro c hc
  refine ⟨fun x => Fin.elim0 x, ?_, false, ?_⟩
  · intro a b
    exact Fin.elim0 a
  · intro u v huv
    exact Fin.elim0 u

/-- The edge-count control for the empty graph computes to zero. -/
theorem emptyGraph_edgeCount :
    edgeCount 0 (⊥ : SimpleGraph (Fin 0)) = 0 := by
  simp [edgeCount]

/-- Sudakov's theorem for Erdős problem #546, formalized with the source's graph
content: for every finite simple graph with no isolated vertices and `m` edges,
its two-colour Ramsey number is bounded by an exponential in the square root of
`m`. The exact proof of Sudakov's result remains an explicit gap.

The source sentence reads: “Let `G` be a graph with no isolated vertices and `m`
edges. Is it true that `R(G) ≤ 2^{O(m^{1/2})}`?” Here `G` is represented by
`G : SimpleGraph (Fin n)`, `m` by `edgeCount n G`, and `R(G)` by
`RamseyNumber n G`. The infimum defining the latter is accompanied above by
proved bounded-below and explicitly recorded nonemptiness controls. -/
theorem sudakov_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (m : ℕ),
        HasNoIsolatedVertices n G →
        edgeCount n G = m →
        (RamseyNumber n G : ℝ) ≤
          (2 : ℝ) ^ (C * Real.sqrt (m : ℝ)) := by
  sorry Erdos546
