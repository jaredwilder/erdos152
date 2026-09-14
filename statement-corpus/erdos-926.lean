/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 4$. Is it true that\[\mathrm{ex}(n;H_k) \ll_k n^{3/2},\]where $H_k$ is the graph on vertices $x,y_1,\ldots,y_k,z_1,\ldots,z_{\binom{k}{2}}$, where $x$ is adjacent to all $y_i$ and each pair of $y_i,y_j$ is adjacent to a unique $z_i$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#926 : [Er69b] [Er71,p.103] [Er74c,p.79] [Er93,p.334] graph theory It is trivial that $\mathrm{ex}(n;H_k)\gg n^{3/2}$ since $H_k$ contians a $C_4$ for $k\geq 3$. Erdős [Er71] claimed a proof for $k=3$. The answer is yes, proved by Füredi [Fu91] , who proved that\[\mathrm{ex}(n;H_k) \ll (kn)^{3/2}.\]This was improved to\[\mathrm{ex}(n;H_k) \ll kn^{3/2}\]by Alon, Krivelevich, and Sudakov [AKS03] . Since each $H_k$ is 2-degenerate this is a special case of [146] . The extremal number of the graph $H_k$ with the vertex $x$ omitted is the subject of [1021] . Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links This page was last edited 05 October 2025. ( View history ) ( The LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #926, https://www.erdosproblems.com/926, accessed 2026-08-30 From the external database . You can help update this.
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos926

/-- The number of vertices in the graph described in the source. -/
def hVertexCount (k : ℕ) : ℕ := 1 + k + Nat.choose k 2

/-- A finite Boolean encoding of the graph pattern `H_k`.  The list of
vertices is required to be pairwise distinct; `x` is adjacent to every
`y`, and every pair of `y` vertices has a common designated `z` vertex.
The injectivity of `z` records the uniqueness requirement. -/
def HFinite (k n : ℕ) (adj : Fin n → Fin n → Bool)
    (x : Fin n) (y : Fin k → Fin n)
    (z : Fin (Nat.choose k 2) → Fin n) : Prop :=
  List.Pairwise (· ≠ ·) (x :: (List.ofFn y ++ List.ofFn z)) ∧
    (∀ i : Fin k, adj x (y i) = true) ∧
    (∀ i j : Fin k, i ≠ j →
      ∃ l : Fin (Nat.choose k 2),
        adj (y i) (z l) = true ∧ adj (y j) (z l) = true) ∧
    Function.Injective z

/-- POSITIVE WITNESS: the complete graph on eleven vertices contains the
finite `H₄` pattern with the displayed vertices. -/
theorem HFinite_witness_pos :
    HFinite 4 11
      (fun a b => decide (a ≠ b))
      0
      ![1, 2, 3, 4]
      ![5, 6, 7, 8, 9, 10] := by
  decide

/-- NEGATIVE WITNESS: the same instance as the positive witness, with exactly
one required edge, the edge from `x` to `y₁`, removed. -/
theorem HFinite_witness_neg :
    ¬ HFinite 4 11
      (fun a b =>
        if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then false
        else decide (a ≠ b))
      0
      ![1, 2, 3, 4]
      ![5, 6, 7, 8, 9, 10] := by
  decide

/-- The graph-theoretic version of containing `H_k`.  A graph on `Fin n`
contains `H_k` when there are pairwise distinct vertices corresponding to
`x`, the `y_i`, and the `z_j`, with the adjacencies specified in the source.
Here the second argument of `G.Adj` is a vertex of the host graph. -/
def ContainsH (k n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ x : Fin n, ∃ y : Fin k → Fin n,
    ∃ z : Fin (Nat.choose k 2) → Fin n,
      List.Pairwise (· ≠ ·) (x :: (List.ofFn y ++ List.ofFn z)) ∧
      (∀ i : Fin k, G.Adj x (y i)) ∧
      (∀ i j : Fin k, i ≠ j →
        ∃ l : Fin (Nat.choose k 2),
          G.Adj (y i) (z l) ∧ G.Adj (y j) (z l)) ∧
      Function.Injective z

/-- The number of edges of a finite simple graph, counted once by ordering
the endpoints. -/
noncomputable def edgeCount (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- The resolved extremal assertion corresponding to the source.  The
notation `≪_k n^{3/2}` is expressed by a constant depending on `k`, an
eventual threshold, and the integer majorant `Nat.sqrt (n^3)`. -/
theorem resolution :
    ∀ k : ℕ, 4 ≤ k →
      ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ G : SimpleGraph (Fin n), ¬ ContainsH k n G →
          edgeCount n G ≤ C * k * Nat.sqrt (n ^ 3) := by
  sorry Erdos926
