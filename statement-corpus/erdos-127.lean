/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(m)$ be maximal such that every graph with $m$ edges must contain a bipartite graph with\[\geq \frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}+f(m)\]edges. Is there an infinite sequence of $m_i$ such that $f(m_i)\to \infty$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#127 : [Er97b] graph theory Conjectured by Erdős, Kohayakava, and Gyárfás. Edwards [Ed73] proved that $f(m)\geq 0$ always. Note that $f(\binom{n}{2})= 0$, taking $K_n$. Solved by Alon [Al96] , who showed $f(n^2/2)\gg n^{1/2}$, and also showed that $f(m)\ll m^{1/4}$ for all $m$. The best possible constant in $f(m)\leq Cm^{1/4}$ is unknown. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #127, https://www.erdosproblems.com/127, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos127

/-- The number of edges of a finite simple graph on `Fin n`. -/
def edgeCount (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

/-- A graph is bipartite when its vertices admit a two-colouring separating every edge. -/
def IsBipartiteGraph (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Bool, ∀ ⦃v w : Fin n⦄, G.Adj v w → c v ≠ c w

/-- `BipartiteSubgraph G H` means that `H` is a subgraph of `G` and is bipartite. -/
def BipartiteSubgraph (G H : SimpleGraph (Fin n)) : Prop :=
  H ≤ G ∧ IsBipartiteGraph H

/-- The numerical term preceding `f(m)` in the source statement. -/
noncomputable def base (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

/-- `Admissible m k` says that every finite simple graph with `m` edges has a
bipartite subgraph with at least `base m + k` edges. -/
def Admissible (m : ℕ) (k : ℝ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    edgeCount G = m →
      ∃ H : SimpleGraph (Fin n),
        BipartiteSubgraph G H ∧
          (edgeCount H : ℝ) ≥ base m + k

/-- The set of all additive improvements that satisfy the universal property
in the source. -/
def AdmissibleSet (m : ℕ) : Set ℝ :=
  {k | Admissible m k}

/-- The function `f` is represented by the supremum of its admissible
improvements.  Since `sSup` has junk values on empty or unbounded sets, the
following two declarations explicitly record the required nonemptiness and
boundedness facts; these are literature-level facts not proved here. -/
noncomputable def f (m : ℕ) : ℝ :=
  sSup (AdmissibleSet m)

/-- The admissible set is nonempty, corresponding to Edwards' lower bound
`f(m) ≥ 0`. -/
theorem admissible_nonempty (m : ℕ) :
    (AdmissibleSet m).Nonempty := by
  sorry

/-- The admissible set is bounded above, so the supremum defining `f(m)` is
not the default value caused by an unbounded set. -/
theorem admissible_bddAbove (m : ℕ) :
    BddAbove (AdmissibleSet m) := by
  sorry

/-- A proved sanity check: the zero-edge threshold admits the empty bipartite
subgraph.  This exercises the graph, bipartiteness, and threshold definitions. -/
theorem admissible_zero_zero : Admissible 0 0 := by
  intro n G hG
  refine ⟨⊥, bot_le, ?_, ?_⟩
  · refine ⟨(fun _ => false), ?_⟩
    intro v w hv
    have hv' : False := hv
    exact hv'.elim
  · simp [edgeCount, base]

#print axioms admissible_zero_zero

/-- The source question: there is a sequence of edge counts along which the
maximal additive improvement tends to infinity. -/
def Question : Prop :=
  ∃ m : ℕ → ℕ, Tendsto (fun i => f (m i)) atTop atTop

/-- The source asks, verbatim, whether there is an infinite sequence
`m_i` with `f(m_i) → ∞`.  The recorded resolution says this is solved by
Alon, via the lower bound `f(n^2/2) ≫ n^(1/2)`.  The proof of that
literature result remains an explicit gap here. -/
theorem solved_question : Question := by
  sorry Erdos127
