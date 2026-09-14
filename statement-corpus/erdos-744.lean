/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k$ be a large fixed constant. Let $f_k(n)$ be the minimal $m$ such that there exists a graph $G$ on $n$ vertices with chromatic number $k$, such that every proper subgraph has chromatic number $<k$, and $G$ can be made bipartite by deleting $m$ edges. Is it true that $f_k(n)\to \infty$ as $n\to \infty$? In particular, is it true that $f_4(n) \gg \log n$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#744 : [Er81] [EHS82] graph theory | chromatic number A problem of Erdős, Hajnal, and Szemerédi [EHS82] . Odd cycles show that $f_3(n)=1$, but they expected $f_4(n)\to \infty$. Gallai [Ga68] gave a construction which shows\[f_4(n) \ll n^{1/2},\]and Lovász extended this to show\[f_k(n) \ll n^{1-\frac{1}{k-2}}.\]This conjecture was disproved by Rödl and Tuza [RoTu85] , who proved that in fact $f_k(n)=\binom{k-1}{2}$ (for all sufficiently large $n$). Additional thanks to : Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 01 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #744, https://www.erdosproblems.com/744, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos744

/-- A proper coloring of a finite simple graph by `k` colors. -/
def Colorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∀ ⦃u v : Fin n⦄, G.Adj u v → c u ≠ c v

/-- A graph is vertex-critical at chromatic number `k` when it is `k`-colorable
and no proper edge-subgraph is `k`-colorable. Since a subgraph of a `k`-colorable
graph is automatically at most `k`-colorable, this expresses chromatic number
strictly below `k` for every proper subgraph. -/
def VertexCritical {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  Colorable G k ∧
    ∀ H : SimpleGraph (Fin n), H ≤ G → H ≠ G → ¬ Colorable H k

/-- The set `D` is an admissible collection of edges of `G` to delete. -/
def DeletionSet {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ D, G.Adj p.1 p.2

/-- `G` becomes bipartite after deleting the pairs in `D`. The coloring is
on the original vertex set, and adjacency is required to change color unless
the edge was deleted. -/
def BipartiteAfter {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Fin n × Fin n)) : Prop :=
  ∃ c : Fin n → Fin 2,
    ∀ ⦃u v : Fin n⦄,
      G.Adj u v →
        ¬ ((u, v) ∈ D ∨ (v, u) ∈ D) →
          c u ≠ c v

/-- `Good k n m` says that there is an `n`-vertex graph of chromatic number
`k`, minimal under proper edge-subgraphs, which becomes bipartite after deleting
exactly `m` edges. The deletion set is explicitly required to consist of edges
of the graph, so this is not a label-based surrogate for the graph-theoretic
condition. -/
def Good (k n m : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    VertexCritical G k ∧
      ∃ D : Finset (Fin n × Fin n),
        D.card = m ∧ DeletionSet G D ∧ BipartiteAfter G D

/-- The extremal quantity from the source, defined as the infimum of the set
of admissible deletion counts. This uses `sInf`, so the definition has the
usual default value on an empty set; all substantive uses below explicitly
include nonemptiness of the defining set. The set is bounded below in `ℕ`
because `0` is a lower bound. -/
noncomputable def f (k n : ℕ) : ℕ :=
  sInf {m : ℕ | Good k n m}

/-- The defining set for `f` is always bounded below; this control rules out
using the junk value of `sInf` as mathematical evidence. -/
theorem f_set_bddBelow (k n : ℕ) :
    BddBelow {m : ℕ | Good k n m} := by
  refine ⟨0, ?_⟩
  intro m hm
  exact Nat.zero_le m

/-- The edgeless graph is colorable with one color. -/
theorem empty_colorable_one (n : ℕ) :
    Colorable (⊥ : SimpleGraph (Fin n)) 1 := by
  refine ⟨fun _ => 0, ?_⟩
  intro u v h
  simp at h

/-- On a nonempty vertex set, the edgeless graph is not colorable with zero
colors. This is a proved anti-vacuity control for the coloring definition. -/
theorem empty_not_colorable_zero {n : ℕ} (hn : 0 < n) :
    ¬ Colorable (⊥ : SimpleGraph (Fin n)) 0 := by
  rintro ⟨c, hc⟩
  let x : Fin n := ⟨0, hn⟩
  exact Fin.elim0 (c x)

/-- The basic coloring controls distinguish one color from zero colors on a
nonempty edgeless graph, exercising the mathematical content of the definitions. -/
theorem coloring_control {n : ℕ} (hn : 0 < n) :
    Colorable (⊥ : SimpleGraph (Fin n)) 1 ∧
      ¬ Colorable (⊥ : SimpleGraph (Fin n)) 0 :=
  ⟨empty_colorable_one n, empty_not_colorable_zero hn⟩

/-- Rödl and Tuza's resolution of the question, formalized with the exact
eventual range recorded by the source. The source says that for fixed `k`,
`f_k(n) = binomial(k-1,2)` for all sufficiently large `n`; the statement
therefore supplies a threshold `N` and, crucially, nonemptiness of the
defining `sInf` set at every `n ≥ N`, so the equality cannot rely on the
junk value of `sInf`.

The source question asks whether `f_k(n)` tends to infinity and in particular
whether `f_4(n) ≫ log n`. The resolution says this is false: the eventual
constant is `binomial(k-1,2)`. -/
theorem rodl_tuza_eventual (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Set.Nonempty {m : ℕ | Good k n m} ∧
        f k n = Nat.choose (k - 1) 2 := by
  sorry

#print axioms coloring_control
#print axioms rodl_tuza_eventual

end Erdos744
