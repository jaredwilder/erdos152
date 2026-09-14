/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(m)$ be the maximal $k$ such that a triangle-free graph on $m$ edges must contain a bipartite graph with $k$ edges. Determine $f(m)$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#581 : [CEG79] graph theory Resolved by Alon [Al96] , who showed that there exist constants $c_1,c_2>0$ such that\[\frac{m}{2}+c_1m^{4/5}\leq f(m)\leq \frac{m}{2}+c_2m^{4/5}.\]See also the entry in the graphs problem collection . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #581, https://www.erdosproblems.com/581, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos581

/-- The number of edges of a finite simple graph, represented as the cardinality
of its finite set of unordered adjacent pairs. -/
noncomputable def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Fintype.card {e : Sym2 V // e ∈ G.edgeSet}

/-- A graph is triangle-free when it has no three pairwise adjacent vertices. -/
def TriangleFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj v w → G.Adj w u → False

/-- A finite simple graph is bipartite when its vertices admit a two-colouring
whose colours differ across every edge. -/
def BipartiteGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Bool, ∀ ⦃u v : V⦄, G.Adj u v → c u ≠ c v

/-- `SubgraphOf H G` means that `H` is a spanning subgraph of `G`, so every
edge of `H` is an edge of `G`. -/
def SubgraphOf {V : Type} (H G : SimpleGraph V) : Prop :=
  ∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v

/-- A natural number `k` is guaranteed for `m` when every finite triangle-free
graph with exactly `m` edges contains a bipartite spanning subgraph with
exactly `k` edges. -/
def Guaranteed (m k : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    edgeCount G = m →
    TriangleFree G →
    ∃ H : SimpleGraph V,
      SubgraphOf H G ∧ BipartiteGraph H ∧ edgeCount H = k

/-- Feasibility records the natural upper bound `k ≤ m` explicitly. This makes
the set used below bounded above, so its `sSup` is not relying on Lean's junk
value for an unbounded set. -/
def Feasible (m k : ℕ) : Prop :=
  k ≤ m ∧ Guaranteed m k

/-- The extremal function asked for in Erdős problem 581, defined as the
supremum of the feasible guaranteed numbers of bipartite edges. -/
noncomputable def extremalValue (m : ℕ) : ℕ :=
  sSup {k : ℕ | Feasible m k}

/-- The zero-edge bipartite subgraph gives the basic nonemptiness control for
the set defining `extremalValue`. -/
theorem feasible_zero (m : ℕ) : Feasible m 0 := by
  refine ⟨Nat.zero_le m, ?_⟩
  intro V _ G _ _
  refine ⟨⊥, ?_, ?_, ?_⟩
  · intro u v h
    exfalso
    simpa using h
  · refine ⟨fun _ => false, ?_⟩
    intro u v h
    exfalso
    simpa using h
  · simp [edgeCount]

/-- The feasible set is bounded above by `m`; hence the `sSup` in the
definition of `extremalValue` is mathematically controlled rather than
taking the default value assigned to an unbounded set. -/
theorem feasible_bddAbove (m : ℕ) :
    BddAbove {k : ℕ | Feasible m k} := by
  refine ⟨m, ?_⟩
  intro k hk
  exact hk.1

/-- The feasible set defining `extremalValue` is nonempty. -/
theorem feasible_nonempty (m : ℕ) :
    Set.Nonempty {k : ℕ | Feasible m k} :=
  ⟨0, feasible_zero m⟩

/-- The proved control for this formalization: zero is always a feasible
guaranteed value, witnessed by the empty bipartite subgraph. -/
theorem zero_is_feasible : Feasible 0 0 :=
  feasible_zero 0

/-- Alon's resolved estimate, stated in its eventual asymptotic form: there
are positive real constants `c₁,c₂` such that for all sufficiently large
natural numbers `m`,
`m/2 + c₁ m^(4/5) ≤ f(m) ≤ m/2 + c₂ m^(4/5)`.
The source records this result as settled; the proof of the literature result
is left as an explicit gap, while the definitions and controls above are
kernel-checked. -/
theorem alon_asymptotic :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᶠ m : ℕ in atTop,
        (m : ℝ) / 2 + c₁ * Real.rpow (m : ℝ) ((4 : ℝ) / 5) ≤
            (extremalValue m : ℝ) ∧
        (extremalValue m : ℝ) ≤
          (m : ℝ) / 2 + c₂ * Real.rpow (m : ℝ) ((4 : ℝ) / 5) := by
  sorry

#print axioms feasible_zero

end Erdos581
