/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 3$ and $n$ be sufficiently large. Is it true that if $G$ is a graph with $n$ vertices and $2n-2$ edges such that every proper induced subgraph has minimum degree $\leq 2$ then $G$ must contain a copy of $C_k$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#815 : [EFGS88] [Er91] graph theory In [Er91] Erdős attributes this to himself and Hajnal, claiming they could prove it for $3\leq k\leq 6$, but it appears in an earlier paper of Erdős, Faudree, Gyárfás, and Schelp [EFGS88] , where they prove that such a graph on $n\geq 5$ vertices contains cycles of length $3$, $4$, and $5$, and a cycle of length at least $\lfloor \log_2n\rfloor$, and need not contain a cycle of length longer than $\sqrt{n}$. Such graphs are called degree $3$ critical. This conjecture was disproved by Narins, Pokrovskiy, and Szabó [NPS17] , who proved that there are arbitrarily large such graphs with no cycle of length $23$. It remains open whether this question has an affirmative answer if we restrict to even $k$. Additional thanks to : Lukas Michel Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #815, https://www.erdosproblems.com/815, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/





-- @category research open








import Mathlib
open Classical Filter

namespace Erdos815

/-- A finite simple graph represented by its Boolean adjacency matrix. -/
def GraphData (n : ℕ) := Fin n → Fin n → Bool

/-- The adjacency matrix is symmetric and has no loops. -/
def IsSimpleGraph {n : ℕ} (G : GraphData n) : Prop :=
  (∀ u v, G u v = G v u) ∧ (∀ u, G u u = false)

/-- The number of unordered edges in a finite Boolean graph. -/
def edgeCount {n : ℕ} (G : GraphData n) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ G p.1 p.2 = true)).card

/-- The successor vertex used when reading a cyclic ordering of `Fin k`. -/
def cycleSuccessor (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- A graph contains a cycle of length `k` when it has an injective cyclic ordering
of `k` vertices whose consecutive vertices are adjacent. -/
def ContainsCycle {n k : ℕ} (G : GraphData n) : Prop :=
  if hk : 0 < k then
    ∃ f : Fin k → Fin n,
      Function.Injective f ∧
        ∀ i : Fin k, G (f i) (f (cycleSuccessor k hk i)) = true
  else
    True

/-- Every nonempty proper induced subgraph has a vertex of induced degree at most two. -/
def DegreeThreeCritical {n : ℕ} (G : GraphData n) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ∃ v ∈ S, (S.filter (fun w => G v w = true)).card ≤ 2

/-- The hypotheses in the source together with the asserted conclusion for one finite
graph. This is a bounded decidable formalization of the question: `G` is the graph
under discussion, and `QuestionFinite n k G` says that the source's hypotheses imply
the existence of its `C_k`. -/
def QuestionFinite (n k : ℕ) (G : GraphData n) : Prop :=
  IsSimpleGraph G ∧ edgeCount G = 2 * n - 2 ∧ DegreeThreeCritical G →
    ContainsCycle G

/-- The source's open question, quantified over all finite graph instances and over
the stipulated range `k ≥ 3`; the phrase "sufficiently large" is represented by
the eventual quantifier on `n`. -/
def Question : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : GraphData n, QuestionFinite n k G

/-- A five-vertex degree-3-critical graph with eight edges, obtained from the
complete graph by deleting the two edges `{0,1}` and `{0,2}`. -/
def positiveGraph : GraphData 5 :=
  fun u v =>
    decide (u ≠ v ∧
      ¬ ((u.val = 0 ∧ v.val = 1) ∨
         (u.val = 1 ∧ v.val = 0) ∨
         (u.val = 0 ∧ v.val = 2) ∨
         (u.val = 2 ∧ v.val = 0)))

/-- POSITIVE WITNESS: this concrete instance satisfies the finite claim for
`k = 3`; its hypotheses hold and it contains a triangle. -/
theorem QuestionFinite_witness_pos :
    QuestionFinite 5 3 positiveGraph := by
  decide

/-- A near-miss instance for the bounded claim: the same graph and the same
criticality hypotheses are tested at cycle length six, which is impossible on
five vertices. -/
theorem QuestionFinite_witness_neg :
    ¬ QuestionFinite 5 6 positiveGraph := by
  decide

/-- The finite graph is genuinely simple, so the positive and negative controls
exercise the graph predicate rather than merely relying on malformed input. -/
theorem positiveGraph_isSimple :
    IsSimpleGraph positiveGraph := by
  decide

/-- The finite graph has exactly the edge count appearing in the source. -/
theorem positiveGraph_edgeCount :
    edgeCount positiveGraph = 2 * 5 - 2 := by
  decide

/-- The finite graph satisfies the source's proper-induced-subgraph minimum-degree
condition. -/
theorem positiveGraph_critical :
    DegreeThreeCritical positiveGraph := by
  decide

end Erdos815

#print axioms Erdos815.QuestionFinite_witness_pos
#print axioms Erdos815.QuestionFinite_witness_neg
