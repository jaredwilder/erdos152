/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph with $1+n(m-1)$ vertices and $1+n\binom{m}{2}$ edges. Must $G$ contain two points which are connected by $m$ disjoint paths?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#915 : [BoEr62] [Er67b,p.4] graph theory A conjecture of Bollobás and Erdős [BoEr62] . This would be the best possible, as demonstrated by $n$ copies of $K_m$ which share a single vertex (but are otherwise disjoint). It is unclear whether disjoint here is to mean edge-disjoint or (internally) vertex-disjoint. The above construction is valid for either interpretation. Let $k_m(n)$ denote the minimum number of edges such that any graph with $n$ vertices and $k_m(n)$ edges contains two vertices which are connected by at least $m$ vertex-disjoint paths. One can similarly consider $\ell_m(n)$, defined similarly but with edge-disjoint paths (so that in particular $\ell_m(n)\leq k_m(n)$). We summarise the known results below, first for $k_m(n)$, then for $\ell_m(n)$. The conjecture in the main problem is that, for all $m\geq 2$,\[k_m(1+(m-1)n)=1+\binom{m}{2}n.\](In particular, $k_m(n)=\frac{m}{2}n+O(1)$.) It is trivial that $k_2(n)=n$. Bártfai [Ba60] proved that $k_3(2n)=3n-1$ and $k_3(2n+1)=3n+1$. Bollobás [Bo66] proved $k_4(n)=2n-1$. Leonard [Le73] disproved this conjecture for $m=5$, giving an explicit counterexample with $57$ vertices and $141$ edges. More generally, Leonard proved the existence of a $c>0$ such that, for all large $n$, $k_5(n)>(\frac{5}{2}+c)n-O(1)$ (an examination of his paper suggests that one can take $c=\frac{3}{80}$). Sørensen and Thomassen [SoTh74] proved that $k_5(n)=\lfloor\frac{8}{3}n\rfloor-3$ for $n\geq 13$. They also prove that the conjectured bound of Bollobás and Erdős holds if the graph is $3$-connected. Mader [Ma73] disproved the conjecture in general, proving that, for all $m\geq 6$ and any $C>0$, there exists an $n$ such that $k_m(n)> \frac{m}{2}n+C$. Sørensen and Thomassen [SoTh74] proved that, for any fixed $m\geq 2$, for infinitely many $n$,\[k_m(n) > \frac{m(m-1)-2}{2m-3}(n-m).\] The results for $\ell_m$ are summarised below. Leonard [Le72] proved $\ell_m(n)=k_m(n)$ for $2\leq m\leq 4$ and $\ell_5(2n)=5n-2$ and $\ell_5(2n+1)=5n+1$. Leonard [Le73b] proved $\ell_6(n)=3n-2$. Mader [Ma73] proved that if a graph with $n$ vertices has\[> \frac{m}{2}(n-1)-\frac{1}{2}(e_0(G)+\cdots+e_{m-2}(G))\]edges then $G$ contains two vertices connected by $m$ edge-disjoint paths (where $e_r(G)$ counts the number of vertices of degree $\leq r$). In particular, this confirms (and is stronger than) the conjecture, and in general establishes\[\ell_m(n)=\left\lfloor \frac{m}{2}(n-1)+1\right\rfloor\]for all $m\geq 2$. Additional thanks to : Sarosh Adenwalla, Stijn Cambie, Jake Mallen, and Terence Tao Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (16) Proof claims (0) More information and links This page was last edited 08 December 2025. ( View history ) ( See the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #915, https://www.erdosproblems.com/915, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None
-/





import Mathlib
open Classical







open Classical Filter

namespace Erdos915

-- @category research open

/-- The internal vertices of a finite simple path, represented by deleting its two endpoints. -/
def internalVertices {V : Type} [DecidableEq V] (p : List V) : Finset V :=
  (p.drop 1).dropLast.toFinset

/-- A list is a simple path from `u` to `v` in `G`. -/
def IsSimplePath {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (p : List V) : Prop :=
  p ≠ [] ∧
    p.head? = some u ∧
    p.getLast? = some v ∧
    p.Chain' G.Adj ∧
    p.Nodup

/-- `HasMDisjointPaths G m` means that some two distinct vertices of `G` are joined by
`m` paths whose internal vertices are pairwise disjoint. The source is ambiguous about
whether “disjoint” means edge-disjoint or internally vertex-disjoint; this definition
chooses the latter reading, which is the reading used for `k_m`. -/
def HasMDisjointPaths {V : Type} [DecidableEq V] (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ u v : V, u ≠ v ∧
    ∃ ps : Fin m → List V,
      (∀ i, IsSimplePath G u v (ps i)) ∧
      (∀ ⦃i j⦄, i ≠ j →
        Disjoint (internalVertices (ps i)) (internalVertices (ps j)))

/-- POSITIVE WITNESS: two vertices in the complete graph on three vertices have one path. -/
theorem hasMDisjointPaths_witness_pos :
    HasMDisjointPaths (⊤ : SimpleGraph (Fin 3)) 1 := by
  refine ⟨0, 1, by decide, (fun _ => [0, 1]), ?_, ?_⟩
  · intro i
    simp [IsSimplePath]
  · intro i j hij
    exact False.elim (hij (Fin subsingleton i j))

/-- NEGATIVE WITNESS: the edgeless graph is a near-miss for the one-path condition,
since it has the required vertices but no edge joining distinct vertices. -/
theorem hasMDisjointPaths_witness_neg :
    ¬ HasMDisjointPaths (⊥ : SimpleGraph (Fin 2)) 1 := by
  rintro ⟨u, v, huv, ps, hps, _⟩
  have hp := hps 0
  rcases hp with ⟨hne, hhead, htail, hchain, hnodup⟩
  have hfirst : u = v := by
    simpa [List.Chain'] using hchain
  exact huv hfirst

/-- The finite edge count appearing in the Erdős--Bollobás question. -/
def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

/-- A graph on `1 + n (m - 1)` vertices satisfies the edge-count hypothesis from the
source when it has exactly `1 + n * choose m 2` edges. -/
def HasSourceCounts (m n : ℕ)
    (G : SimpleGraph (Fin (1 + n * (m - 1)))) : Prop :=
  edgeCount G = 1 + n * (Nat.choose m 2)

/-- POSITIVE WITNESS: the complete graph on three vertices has the required three edges
for `m = 2` and `n = 2`. -/
theorem hasSourceCounts_witness_pos :
    HasSourceCounts 2 2 (⊤ : SimpleGraph (Fin 3)) := by
  decide

/-- NEGATIVE WITNESS: deleting one edge from the positive three-vertex instance gives
a near-miss, violating exactly the edge-count condition by one. -/
theorem hasSourceCounts_witness_neg :
    ¬ HasSourceCounts 2 2 (⊥ : SimpleGraph (Fin 3)) := by
  decide

/-- The open question from the source, under the internally vertex-disjoint interpretation:
every graph with the displayed number of vertices and edges contains two vertices joined
by `m` internally vertex-disjoint paths.

SOURCE MAPPING: the source asks whether a graph with `1 + n (m - 1)` vertices and
`1 + n choose m 2` edges must contain the stated paths. The present statement uses
`HasSourceCounts` for the numerical hypotheses and `HasMDisjointPaths` for the conclusion.
The resolution records that the conjecture is false for `m = 5` and in general for
`m ≥ 6`, so this declaration is intentionally an open source question rather than a
proved theorem. -/
theorem bollobas_erdos_question :
    ∀ m n : ℕ, m ≥ 2 →
      ∀ G : SimpleGraph (Fin (1 + n * (m - 1))),
        HasSourceCounts m n G → HasMDisjointPaths G m := by
  sorry Erdos915
