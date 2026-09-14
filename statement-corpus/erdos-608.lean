/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph with $n$ vertices and $>n^2/4$ many edges. Are there at least $\frac{2}{9}n^2$ edges of $G$ which are contained in a $C_5$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#608 : [EFR92] [Er97d] graph theory Erdős, Faudree, and Rousseau [EFR92] proved that any graph on $n$ vertices with $>n^2/4$ edges contains at least $2\lfloor n/2\rfloor+1$ edges in triangles. Erdős [Er97d] stated that, under the same assumptions, there at least $\frac{2}{9}n^2$ edges of $G$ which are contained in some odd cycle - this is best possible, as witnessed by taking a complete graph on $\lfloor \frac{2n+4}{3}\rfloor$ and a complete balanced bipartite graph on $\lfloor \frac{n+1}{3}\rfloor$ vertices, which overlap on exactly one vertex. Erdős wrote that a positive answer to this question would follow if we knew that $G$ must contain a triangle such that there at least $n/2-O(1)$ vertices joined to at least two vertices of the triangle. Erdős and Faudree observed that every graph with $2n$ vertices and at least $n^2+1$ edges has a triangle whose vertices are joined to at least $n+2$ vertices. Erdős, Faudree, and Rousseau [EFR92] ask, more generally, if for any fixed $k\geq 2$ every graph with $n$ vertices and $>n^2/4$ edges contains at least $\frac{2}{9}n^2-O_k(n)$ edges which are contained in a $C_{2k+1}$. The answer to the original question with $C_5$ is no - Füredi and Maleki (in unpublished work which is described by Grzesik, Hu, and Volec [GHV19] ) have constructed graphs with $n$ vertices and $>n^2/4$ edges in which the number of edges contained in a $C_5$ is at most $cn^2+O(n)$ where\[c=\frac{2+\sqrt{2}}{16}\approx 0.2134.\]This is the best possible: Grzesik, Hu, and Volec [GHV19] have proved that a graph on $n$ vertices with $>n^2/4$ edges contains at least $(c-o(1))n^2$ edges in a $C_5$. They further prove the conjecture of Erdős, Faudree, and Rousseau [EFR92] for all $k\geq 3$ (that $>n^2/4$ edges ensures at least $\frac{2}{9}n^2-O(n)$ edges in a $C_{2k+1}$). See also the entry in the graphs problem collection . Additional thanks to : Quanyu Tang Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 25 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #608, https://www.erdosproblems.com/608, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None
-/





import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos608

/-- The successor map on the cyclic index set for a 5-cycle. -/
def next5 (i : Fin 5) : Fin 5 :=
  ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

/-- An edge is contained in a copy of `C₅` when it is one of the five
edges of an injectively parametrized cyclic 5-vertex subgraph. -/
def EdgeInC5 {n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin n) : Prop :=
  ∃ v : Fin 5 → Fin n,
    Function.Injective v ∧
      (∀ i : Fin 5, G.Adj (v i) (v (next5 i))) ∧
      ∃ i : Fin 5,
        (a = v i ∧ b = v (next5 i)) ∨
        (b = v i ∧ a = v (next5 i))

/-- The number of edges of a finite graph, represented by the unique ordered
pair `(a,b)` with `a < b` for each undirected edge. -/
def edgeCount (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)
    Finset.univ).card

/-- The number of edges that are contained in a copy of `C₅`. -/
def c5EdgeCount (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧
      EdgeInC5 G p.1 p.2)
    Finset.univ).card

/-- The literal formalization of the original question, using integer-scaled
inequalities to avoid division: more than `n²/4` edges means
`4 * edgeCount > n²`, and at least `2n²/9` edges means
`9 * c5EdgeCount ≥ 2n²`. -/
def OriginalQuestion : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    4 * edgeCount n G > n * n →
      9 * c5EdgeCount n G ≥ 2 * n * n

/-- The empty graph on `Fin n`, used for a proved sanity check on the
edge-counting definitions. -/
def emptyGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj := fun _ _ => False
  symm := by
    intro a b hab
    exact hab
  loopless := by
    intro a haa
    exact haa

/-- Sanity control: the edge counter gives zero on the explicitly defined
empty graph. -/
theorem edgeCount_empty (n : ℕ) :
    edgeCount n (emptyGraph n) = 0 := by
  simp [edgeCount, emptyGraph]

/-- Sanity control: the empty graph cannot satisfy the strict density
hypothesis from the source. -/
theorem emptyGraph_not_dense (n : ℕ) :
    ¬ (4 * edgeCount n (emptyGraph n) > n * n) := by
  simp [edgeCount, emptyGraph]

/-- The source's resolution says that the original `C₅` assertion is false.
The formal proof of the counterexample construction and its edge-count
estimate remains to be supplied; this declaration records that honest gap
rather than introducing an axiom. -/
theorem original_question_is_false : ¬ OriginalQuestion := by
  sorry Erdos608

#print axioms Erdos608.edgeCount_empty
#print axioms Erdos608.emptyGraph_not_dense
