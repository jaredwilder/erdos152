/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Does every graph with infinite chromatic number contain a cycle of length $2^n$ for infinitely many $n$?

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#63 : [Er93,p.342] [Er94b] [Er95] [Er95d] [Er96] [Er97b] graph theory | chromatic number | cycles Conjectured by Mihók and Erdős. It is likely that $2^n$ can be replaced by any sufficiently quickly growing sequence (e.g. the squares). David Penman has observed that this is certainly true if the graph has uncountable chromatic number, since by a result of Erdős and Hajnal [ErHa66] such a graph must contain arbitrarily large finite complete bipartite graphs (see also Theorem 3.17 of Reiher [Re24] ). Zach Hunter has observed that this follows from the work of Liu and Montgomery [LiMo20] : if $G$ has infinite chromatic number then, for infinitely many $r$, it must contain some finite connected subgraph $G_r$ with chromatic number $r$ (via the de Bruijn-Erdős theorem [dBEr51] ). Each $G_r$ contains some subgraph $H_r$ with minimum degree at least $r-1$, and hence via Theorem 1.1 of [LiMo20] there exists some $\ell_r\geq r^{1-o(1)}$ such that $H_r$ contains a cycle of every even length in $[(\log \ell)^8,\ell]$. See also [64] . Additional thanks to : Zach Hunter and David Penman Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #63, https://www.erdosproblems.com/63, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next <!-- Different menu on mob
-/

import Mathlib

-- @category research solved

namespace ErdosProblem63

/-- A simple undirected graph, with its vertex type and adjacency relation made explicit. -/
structure EGraph where
  V : Type
  adj : V → V → Prop
  symm : ∀ ⦃u v : V⦄, adj u v → adj v u
  loopless : ∀ ⦃u : V⦄, ¬ adj u u

/-- A proper coloring of a graph by `k` colors. -/
def ProperColoring (G : EGraph) (k : ℕ) (c : G.V → Fin k) : Prop :=
  ∀ ⦃u v : G.V⦄, G.adj u v → c u ≠ c v

/-- A graph has infinite chromatic number when it has no proper coloring by any
finite number of colors. -/
def InfiniteChromatic (G : EGraph) : Prop :=
  ∀ k : ℕ, ¬ ∃ c : G.V → Fin k, ProperColoring G k c

/-- `HasCycle G L` means that `G` contains a simple cycle of length `L`.
The positivity witness is included so that the cyclic successor is well-defined. -/
def HasCycle (G : EGraph) (L : ℕ) : Prop :=
  ∃ hL : 0 < L,
    ∃ f : Fin L → G.V,
      Function.Injective f ∧
        ∀ i : Fin L,
          G.adj (f i)
            (f ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩)

/-- The formalization of the source question:
“Does every graph with infinite chromatic number contain a cycle of length
`2^n` for infinitely many `n`?”  The source's `2^n` is represented by
`2 ^ n`, and “for infinitely many” is represented by infinitude of the
corresponding set of natural numbers. -/
def Erdos63Question : Prop :=
  ∀ G : EGraph,
    InfiniteChromatic G →
      Set.Infinite {n : ℕ | HasCycle G (2 ^ n)}

/-- The cycle predicate itself records that every admitted cycle has positive
length; this is a proved sanity check on the formalization. -/
theorem cycle_length_positive (G : EGraph) (L : ℕ)
    (h : HasCycle G L) : 0 < L := by
  exact h.choose

/-- No graph contains a cycle of length zero under the definition above. -/
theorem no_zero_cycle (G : EGraph) : ¬ HasCycle G 0 := by
  intro h
  have hp : 0 < 0 := h.choose
  exact (Nat.lt_irrefl 0) hp

/-- The empty graph does not have infinite chromatic number, since it admits
a coloring with one color. -/
def emptyEGraph : EGraph where
  V := Empty
  adj := fun _ _ => False
  symm := by
    intro u v h
    exact h
  loopless := by
    intro u h
    exact h

/-- A proved control exercising the definitions of finite coloring and infinite
chromatic number: the empty graph is not infinitely chromatic. -/
theorem empty_not_infiniteChromatic :
    ¬ InfiniteChromatic emptyEGraph := by
  intro h
  have hn := h 1
  apply hn
  refine ⟨(fun x => Empty.elim x), ?_⟩
  intro u v huv
  exact Empty.elim u

#print axioms cycle_length_positive
#print axioms no_zero_cycle
#print axioms empty_not_infiniteChromatic

end ErdosProblem63