/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 3$. Is it true that, if $m$ is sufficiently large, for any graph $H$ on $m$ edges without isolated vertices,\[R(C_k,H) \leq 2m+\left\lfloor\frac{k-1}{2}\right\rfloor?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#570 : [EFRS93,p.399] graph theory | ramsey theory This is Question 5 of [EFRS93] . This was proved for even $k$ by Erdős, Faudree, Rousseau, and Schelp [EFRS93] . This was proved for $k=3$ independently by Goddard and Kleitman [GoKl94] and Sidorenko [Si91] . This was proved for $k=5$ by Jayawardene [Ja99] . Finally it was proved for all odd $k\geq 7$ by Cambie, Freschi, Morawski, Petrova, and Pokrovskiy [CFMPP26] . This problem is #35 in Ramsey Theory in the graphs problem collection. Additional thanks to : Stijn Cambie Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 16 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #570, https://www.erdosproblems.com/570, accessed 2026-08-30 From the external database . You can help update this. Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos570

/-- A finite graph has the number of edges given by the cardinality of its edge finset. -/
noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

/-- A graph has no isolated vertices when every vertex has a neighbour. -/
def NoIsolated {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ w : V, G.Adj v w

/-- `HasCycle k G` says that `G` contains a cyclically ordered copy of the
cycle of length `k`, with indices in `ZMod k`. -/
def HasCycle (k : ℕ) {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : ZMod k → V,
    Function.Injective f ∧
      ∀ i : ZMod k, G.Adj (f i) (f (i + 1))

/-- `Embeds G H` means that the graph `G` occurs as a (not necessarily induced)
subgraph of `H`, via an injective edge-preserving map. -/
def Embeds {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W,
    Function.Injective f ∧
      ∀ ⦃v w : V⦄, G.Adj v w → H.Adj (f v) (f w)

/-- A pair of graphs on the same vertex set is a two-colouring of the complete
graph when every pair of distinct vertices receives exactly one colour. -/
def IsTwoColoring {V : Type*} (red blue : SimpleGraph V) : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w →
    (red.Adj v w ∨ blue.Adj v w) ∧ ¬ (red.Adj v w ∧ blue.Adj v w)

/-- The Ramsey property at `N`: every red-blue colouring of `K_N` contains
a red `k`-cycle or a blue copy of `H`. -/
def RamseyAt (k : ℕ) {V : Type*} (H : SimpleGraph V) (N : ℕ) : Prop :=
  ∀ (red blue : SimpleGraph (Fin N)),
    IsTwoColoring red blue →
      (HasCycle k red ∨ Embeds H blue)

/-- This is the assertion `R(C_k,H) ≤ B`, expressed directly by the existence
of a valid Ramsey host of order at most `B`; avoiding an `sInf` definition
also avoids the empty-set default value of `sInf`. -/
def RamseyBound (k : ℕ) {V : Type*} (H : SimpleGraph V) (B : ℕ) : Prop :=
  ∃ N : ℕ, N ≤ B ∧ RamseyAt k H N

/-- A proved sanity check: the empty graph on the empty finite vertex type has
zero edges and has no isolated vertices. -/
theorem empty_graph_control :
    edgeCount (⊥ : SimpleGraph (Fin 0)) = 0 ∧
      NoIsolated (⊥ : SimpleGraph (Fin 0)) := by
  constructor
  · simp [edgeCount]
  · intro v
    exact Fin.elim0 v

/-- The source asks for “there exist a threshold beyond which, for every
`k`-edge-cycle parameter and every finite graph `H` with `m` edges and no
isolated vertices, the Ramsey number is at most
`2 * m + floor ((k - 1) / 2)`.”

Here `RamseyBound k H B` is the direct formal reading of `R(C_k,H) ≤ B`,
and the natural-number division `(k - 1) / 2` is the floor appearing in the
source. The resolution node records that the assertion is proved for every
allowed `k`; the proof of that external graph-theoretic theorem remains to be
formalized. -/
theorem erdos_570 :
    ∀ k : ℕ, 3 ≤ k →
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ∀ {V : Type*} [Fintype V] (H : SimpleGraph V),
          edgeCount H = m →
          NoIsolated H →
          RamseyBound k H (2 * m + (k - 1) / 2) := by
  sorry

#print axioms empty_graph_control

end Erdos570
