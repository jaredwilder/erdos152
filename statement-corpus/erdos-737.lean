/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph with chromatic number $\aleph_1$. Must there exist an edge $e$ such that, for all large $n$, $G$ contains a cycle of length $n$ containing $e$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#737 : [EHS74] [Er81] graph theory | chromatic number A problem of Erdős, Hajnal, and Shelah [EHS74] , who proved that $G$ must contain all sufficiently large cycles (see [594] ). This is true, and was proved by Thomassen [Th83] . Additional thanks to : Boris Alexeev Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 01 October 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #737, https://www.erdosproblems.com/737, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos737

/-- A proper coloring of a simple graph using a cardinal number `κ` of colors. -/
def Colorable {V : Type} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ c : V → Cardinal.toType κ, ∀ ⦃x y : V⦄, G.Adj x y → c x ≠ c y

/-- The graph has chromatic number exactly `ℵ₁`, expressed as colorability by `ℵ₁`
and non-colorability by every strictly smaller cardinal. -/
def ChromaticNumberAlephOne {V : Type} (G : SimpleGraph V) : Prop :=
  Colorable G (Cardinal.aleph 1) ∧
    ∀ κ : Cardinal, κ < Cardinal.aleph 1 → ¬ Colorable G κ

/-- A pair of vertices occurs as an oriented edge of a cyclic ordering of `Fin n`. -/
def IsEdgeOnCycle {V : Type} {n : ℕ} (v : Fin n → V) (e : V × V) (hn : 0 < n) : Prop :=
  (∃ i : Fin (n - 1),
      (v i.castSucc = e.1 ∧ v i.succ = e.2) ∨
      (v i.castSucc = e.2 ∧ v i.succ = e.1)) ∨
    ((v ⟨n - 1, by omega⟩ = e.1 ∧ v 0 = e.2) ∨
      (v ⟨n - 1, by omega⟩ = e.2 ∧ v 0 = e.1))

/-- `CycleThrough G e n` means that the genuine simple graph `G` has a
cycle of length `n` containing the edge represented by the ordered pair `e`.
The cyclic ordering is injective, consecutive vertices are adjacent, and the
last vertex is adjacent to the first. -/
def CycleThrough {V : Type} (G : SimpleGraph V) (e : V × V) (n : ℕ) : Prop :=
  ∃ hn : 0 < n, ∃ v : Fin n → V,
    Function.Injective v ∧
      (∀ i : Fin (n - 1), G.Adj (v i.castSucc) (v i.succ)) ∧
      G.Adj (v ⟨n - 1, by omega⟩) (v 0) ∧
      IsEdgeOnCycle v e hn

/-- A proved control: every edge certified as lying on a cycle is actually an
edge of the graph. -/
theorem cycleThrough_edge_control {V : Type} {G : SimpleGraph V}
    {e : V × V} {n : ℕ} (h : CycleThrough G e n) : G.Adj e.1 e.2 := by
  rcases h with ⟨hn, v, hv, hpath, hlast, hedge⟩
  rcases hedge with ⟨i, hi⟩ | hi
  · rcases hi with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [← h₁, ← h₂]
      exact hpath i
    · rw [← h₁, ← h₂]
      exact hpath i
  · rcases hi with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [← h₁, ← h₂]
      exact hlast
    · rw [← h₁, ← h₂]
      exact hlast

/-- A proved control for the coloring definition: a proper coloring separates
the colors of the endpoints of every edge. -/
theorem coloring_separates {V : Type} {G : SimpleGraph V} {κ : Cardinal}
    (h : Colorable G κ) {x y : V} (hxy : G.Adj x y) :
    ∃ c : V → Cardinal.toType κ, c x ≠ c y := by
  rcases h with ⟨c, hc⟩
  exact ⟨c, hc hxy⟩

/-- Thomassen's theorem resolving the source question.

SOURCE-TO-LEAN MAPPING:
The source asks for an edge `e` such that, for all sufficiently large natural
numbers `n`, there is a cycle of length `n` containing `e`. The predicate
`ChromaticNumberAlephOne` records chromatic number exactly `ℵ₁`, while
`CycleThrough` records an injective cyclic ordering with graph edges between
successive vertices and with `e` among those cycle edges. The resolution node
states that this is true, proved by Thomassen. -/
theorem thomassen_cycle_edge :
    ∀ (V : Type) (G : SimpleGraph V),
      ChromaticNumberAlephOne G →
        ∃ e : V × V, G.Adj e.1 e.2 ∧
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n → CycleThrough G e n := by
  sorry Erdos737
