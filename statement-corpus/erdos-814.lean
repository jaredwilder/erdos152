/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 2$ and $G$ be a graph with $n\geq k-1$ vertices and\[(k-1)(n-k+2)+\binom{k-2}{2}+1\]edges. Does there exist some $c_k>0$ such that $G$ must contain an induced subgraph on at most $(1-c_k)n$ vertices with minimum degree at least $k$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#814 : [EFRS90] [Er91] [Er93,p.344] graph theory The case $k=3$ was a problem of Erdős and Hajnal [Er91] . The question for general $k$ was a conjecture of Erdős, Faudree, Rousseau, and Schelp [EFRS90] , who proved that such a subgraph exists with at most $n-c_k\sqrt{n}$ vertices. Mousset, Noever, and Skorić [MNS17] improved this to\[n-c_k\frac{n}{\log n}.\]The full conjecture was proved by Sauermann [Sa19] , who proved this with $c_k \gg 1/k^3$. Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #814, https://www.erdosproblems.com/814, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




-- @category research solved






import Mathlib
open Classical Filter

namespace Erdos814

/-- A finite graph has minimum degree at least `k` when every vertex has at least
`k` neighbors. -/
def MinDegreeAtLeast {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v, k ≤ G.degree v

/-- `HasSmallInducedMinDegree G k` says that `G` has an induced subgraph
whose vertex set has cardinality at most four fifths of the ambient cardinality
and whose minimum degree is at least `k`. -/
def HasSmallInducedMinDegree (n k : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ S : Finset (Fin n),
    5 * S.card ≤ 4 * n ∧
      MinDegreeAtLeast (G.induce (S : Set (Fin n))) k

/-- A finite test instance for the conjecture, using the concrete constant
`c = 1/5` and equality in the displayed edge threshold.  This is a decidable
finite control predicate, not the full asymptotic conjecture. -/
def FiniteClaim (k n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  k ≥ 2 ∧
    n ≥ k - 1 ∧
    (k - 1) * (n - k + 2) + Nat.choose (k - 2) 2 + 1 ≤ G.edgeFinset.card ∧
    HasSmallInducedMinDegree n k G

/-- POSITIVE WITNESS: the complete graph on five vertices satisfies the
finite control instance for `k = 3`. -/
theorem FiniteClaim_witness_pos :
    FiniteClaim 3 5 (⊤ : SimpleGraph (Fin 5)) := by
  decide

/-- NEGATIVE WITNESS: reducing the complete positive instance to four vertices
breaks exactly the edge-threshold condition, since the threshold is eight
while a simple graph on four vertices has at most six edges. -/
theorem FiniteClaim_witness_neg :
    ¬ FiniteClaim 3 4 (⊤ : SimpleGraph (Fin 4)) := by
  decide

/-- The full conjecture, in the direction recorded by the source: for each
`k ≥ 2` there is a positive real constant `c` such that every graph on
`n ≥ k - 1` vertices with at least
`(k-1)(n-k+2) + binom(k-2,2) + 1` edges has an induced subgraph on at most
`(1-c)n` vertices and minimum degree at least `k`.

The source clause reads “there exist some `c_k > 0` such that `G` must contain
an induced subgraph on at most `(1-c_k)n` vertices”; the formal statement maps
`G` to the host graph, `S` to the vertex set of the induced subgraph, and
`G.induce S` to that induced subgraph. The resolution records this as proved by
Sauermann, with the quantitative information `c_k ≫ 1/k^3`. -/
theorem sauermann_resolution :
    ∀ k : ℕ, k ≥ 2 →
      ∃ c : ℝ, 0 < c ∧
        ∀ n : ℕ, n ≥ k - 1 →
          ∀ G : SimpleGraph (Fin n),
            (k - 1) * (n - k + 2) + Nat.choose (k - 2) 2 + 1 ≤
                G.edgeFinset.card →
              ∃ S : Finset (Fin n),
                (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
                  MinDegreeAtLeast (G.induce (S : Set (Fin n))) k := by
  sorry

#print axioms FiniteClaim_witness_pos
#print axioms FiniteClaim_witness_neg

end Erdos814
