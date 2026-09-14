/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $r\geq 3$ and $k$ be sufficiently large in terms of $r$. Is it true that every $r$-uniform hypergraph with chromatic number $k$ has at least\[\binom{(r-1)(k-1)+1}{r}\]edges, with equality only for the complete graph on $(r-1)(k-1)+1$ vertices?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#832 : [Er74d] graph theory | hypergraphs | chromatic number When $r=2$ it is a classical fact that chromatic number $k$ implies at least $\binom{k}{2}$ edges. Erdős asked for $k$ to be large in this conjecture since he knew it to be false for $r=k=3$, as witnessed by the Steiner triples with $7$ vertices and $7$ edges. This was disproved by Alon [Al85] , who proved, for example, that there exists some absolute constant $C>0$ such that if $r\geq C$ and $k\geq Cr$ then there exists an $r$-uniform hypergraph with chromatic number $\geq k$ with at most\[\leq (7/8)^r\binom{(r-1)(k-1)+1}{r}\]many edges. In general, Alon gave an upper bound for the minimal number of edges using Turán numbers. Using known bounds for Turán numbers then suffices to disprove this conjecture for all $r\geq 4$. The validity of this conjecture for $r=3$ remains open. If $m(r,k)$ denotes the minimal number of edges of any $r$-uniform hypergraph with chromatic number $>k$ then Akolzin and Shabanov [AkSh16] have proved\[\frac{r}{\log r}k^r \ll m(r,k) \ll (r^3\log r) k^r,\]where the implied constants are absolute. Cherkashin and Petrov [ChPe20] have proved that, for fixed $r$, $m(r,k)/k^r$ converges to some limit as $k\to \infty$. Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #832, https://www.erdosproblems.com/832, accessed 2026-08-30 From the external database . Formalised statement? No
-/




import Mathlib
open Classical

-- @category research open







open Classical Filter

namespace Erdos832

/-- An `r`-uniform hypergraph on `Fin n` is represented by its finite edge set. -/
def IsUniform (r n : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = r

/-- POSITIVE WITNESS: the two edges of a path are uniformly two-element edges. -/
theorem IsUniform_witness_pos :
    IsUniform 2 3
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) := by
  decide

/-- NEGATIVE WITNESS: the near-miss replaces one two-element edge by a singleton. -/
theorem IsUniform_witness_neg :
    ¬ IsUniform 2 3
      ({({0, 1} : Finset (Fin 3)), ({1} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) := by
  decide

/-- A coloring is proper when every edge contains two vertices of different colors. -/
def IsProperColoring {n k : ℕ} (H : Finset (Finset (Fin n)))
    (c : Fin n → Fin k) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- POSITIVE WITNESS: the path is properly colored with two colors. -/
theorem IsProperColoring_witness_pos :
    IsProperColoring
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3)))
      (fun i : Fin 3 => if i = 1 then 1 else 0) := by
  decide

/-- NEGATIVE WITNESS: the same path with the near-miss constant coloring is not proper. -/
theorem IsProperColoring_witness_neg :
    ¬ IsProperColoring
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3)))
      (fun _ : Fin 3 => 0) := by
  decide

/-- `HasProperColoring H k` means that `H` has a proper coloring with `k` colors. -/
def HasProperColoring {n k : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ c : Fin n → Fin k, IsProperColoring H c

/-- POSITIVE WITNESS: the displayed path has a proper coloring with two colors. -/
theorem HasProperColoring_witness_pos :
    HasProperColoring
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) 2 := by
  decide

/-- NEGATIVE WITNESS: the same path has no proper coloring with one color. -/
theorem HasProperColoring_witness_neg :
    ¬ HasProperColoring
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) 1 := by
  decide

/-- `ChromaticAtLeast H k` means that no proper coloring with `k - 1` colors exists. -/
def ChromaticAtLeast {n k : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ¬ HasProperColoring H (k - 1)

/-- POSITIVE WITNESS: the path is not one-colorable. -/
theorem ChromaticAtLeast_witness_pos :
    ChromaticAtLeast
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) 2 := by
  decide

/-- NEGATIVE WITNESS: deleting all edges gives a one-colorable near-miss. -/
theorem ChromaticAtLeast_witness_neg :
    ¬ ChromaticAtLeast (∅ : Finset (Finset (Fin 3))) 2 := by
  decide

/-- `ChromaticExactly H k` expresses chromatic number exactly `k` in the finite model. -/
def ChromaticExactly {n k : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ChromaticAtLeast H k ∧ HasProperColoring H k

/-- POSITIVE WITNESS: the two-edge path has chromatic number exactly two. -/
theorem ChromaticExactly_witness_pos :
    ChromaticExactly
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) 2 := by
  decide

/-- NEGATIVE WITNESS: the same path does not have chromatic number exactly three. -/
theorem ChromaticExactly_witness_neg :
    ¬ ChromaticExactly
      ({({0, 1} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) 3 := by
  decide

/-- The complete `r`-uniform hypergraph on `Fin n`. -/
def CompleteEdges (r n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun e => e.card = r)

/-- The number of edges of a finite hypergraph. -/
def EdgeCount {n : ℕ} (H : Finset (Finset (Fin n))) : ℕ :=
  H.card

/-- The finite lower-bound question at fixed parameters and fixed vertex size. -/
def FiniteLowerBound (r k n : ℕ) : Prop :=
  ∀ H : Finset (Finset (Fin n)),
    IsUniform r n H →
    ChromaticExactly H k →
    EdgeCount H ≥ Nat.choose ((r - 1) * (k - 1) + 1) r

/-- POSITIVE WITNESS: the classical graph case on two vertices satisfies the bound. -/
theorem FiniteLowerBound_witness_pos :
    FiniteLowerBound 2 2 2 := by
  decide

/-- NEGATIVE WITNESS: a near-miss three-uniform instance violates the literal small-parameter bound. -/
theorem FiniteLowerBound_witness_neg :
    ¬ FiniteLowerBound 3 3 7 := by
  decide

/-- 
`Question832 r k` is the literal finite-vertex formulation of the source question,
with “sufficiently large in terms of `r`” represented by the explicit guard `r ≤ k`.
The source resolution says this assertion is false for `r ≥ 4`, while the case `r = 3`
remains open. The equality-only clause is stated using the complete edge set on exactly
the extremal number of vertices.
-/
def Question832 (r k : ℕ) : Prop :=
  r ≥ 3 ∧ r ≤ k ∧
    ∀ n : ℕ, ∀ H : Finset (Finset (Fin n)),
      IsUniform r n H →
      ChromaticExactly H k →
      EdgeCount H ≥ Nat.choose ((r - 1) * (k - 1) + 1) r ∧
      (EdgeCount H = Nat.choose ((r - 1) * (k - 1) + 1) r →
        n = (r - 1) * (k - 1) + 1 ∧
        H = CompleteEdges r n)

/-- The source question is recorded as an open research proposition, not asserted as a theorem. -/
theorem question832_status : Question832 3 3 := by
  sorry Erdos832
