/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that, for every $c>0$, there exists $f(c)$ such that every graph on $n$ vertices with at least $\lfloor n^2/4\rfloor+k$ edges, where $k<c n$, contains at least $k-f(c)$ many edge disjoint triangles?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#1009 : [Er71,p.98] graph theory Erdős proved this for $c<1/2$ using a theorem of Erdős and Gallai, which says that every graph on $n$ vertices with at least $(n-1)^2/4+2$ many edges, with chromatic number $3$, must contain a triangle. In fact, Erdős proved this is true with $f(c)=0$ for $c<1/2$. At first Erdős thought $f(c)=0$ for larger values of $c$ but this is false: an example of Sauer proves that $f(2)\geq 1$. Sauer gave an example of a graph on $n$ vertices with $\lfloor n^2/4\rfloor+2n-6$ many edges which contains only $2n-7$ many edge disjoint triangles: if $n=2r+4$ then $G$ is the complete tripartite graph on $[r]\times [r]\times [4]$, with a $K_4$ on the $[4]$ vertices also. This is true, and was proved by Györi [Gy88] who proved that this is true with $f(c)\ll c^2$, and also that $f(c)=0$ if $c<2$ for odd $n$ or $c<3/2$ for even $n$. Additional thanks to : Stijn Cambie Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 31 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #1009, https://www.erdosproblems.com/1009, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos1009

/-- An ordered triple of vertices used to represent a triangle. -/
def Triple (n : ℕ) := Fin n × Fin n × Fin n

/-- The number of unordered edges of a finite simple graph, represented by pairs in increasing order. -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card

/-- A triangle is a triple of distinct vertices whose three pairs are adjacent. -/
def Triangle {n : ℕ} (G : SimpleGraph (Fin n)) (t : Triple n) : Prop :=
  t.1 ≠ t.2.1 ∧
    t.1 ≠ t.2.2 ∧
    t.2.1 ≠ t.2.2 ∧
    G.Adj t.1 t.2.1 ∧
    G.Adj t.1 t.2.2 ∧
    G.Adj t.2.1 t.2.2

/-- The finite set of canonical vertex pairs that can represent edges. -/
def edgePairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2)

/-- A triangle pack is a finite family of triangles such that no edge occurs in two
different members. -/
def trianglePack {n : ℕ} (G : SimpleGraph (Fin n)) (P : Finset (Triple n)) : Prop :=
  (∀ t ∈ P, Triangle G t) ∧
    (∀ t ∈ P, ∀ u ∈ P, t ≠ u →
      ∀ e ∈ edgePairs n,
        ((e.1 = t.1 ∨ e.1 = t.2.1 ∨ e.1 = t.2.2) ∧
          (e.2 = t.1 ∨ e.2 = t.2.1 ∨ e.2 = t.2.2)) →
        ¬ ((e.1 = u.1 ∨ e.1 = u.2.1 ∨ e.1 = u.2.2) ∧
          (e.2 = u.1 ∨ e.2 = u.2.1 ∨ e.2 = u.2.2)))

/-- POSITIVE WITNESS: the three vertices of the complete graph on three vertices form a triangle. -/
theorem triangle_witness_pos :
    Triangle (⊤ : SimpleGraph (Fin 3)) ((0, 1, 2) : Triple 3) := by
  decide

/-- NEGATIVE WITNESS: repeating one vertex is a near-miss that fails exactly the distinctness
condition while retaining the ambient complete graph. -/
theorem triangle_witness_neg :
    ¬ Triangle (⊤ : SimpleGraph (Fin 3)) ((0, 0, 2) : Triple 3) := by
  decide

/-- POSITIVE WITNESS: the singleton family containing the triangle on three vertices is
an edge-disjoint triangle pack. -/
theorem trianglePack_witness_pos :
    trianglePack (⊤ : SimpleGraph (Fin 3))
      ({((0, 1, 2) : Triple 3)} : Finset (Triple 3)) := by
  decide

/-- NEGATIVE WITNESS: replacing the valid triangle by a repeated-vertex near miss destroys
the triangle-pack condition. -/
theorem trianglePack_witness_neg :
    ¬ trianglePack (⊤ : SimpleGraph (Fin 3))
      ({((0, 0, 2) : Triple 3)} : Finset (Triple 3)) := by
  decide

/-- CONTROL: the complete graph on three vertices has exactly three canonical edges. -/
theorem edgeCount_control :
    edgeCount (⊤ : SimpleGraph (Fin 3)) = 3 := by
  decide

/-- Erdős problem 1009, formalized with finite simple graphs on `Fin n`.
The source clause “there exists `f(c)` such that every graph ... contains at least
`k-f(c)` many edge disjoint triangles” is read as the existence of a natural-valued
error term for every positive real `c`, with `edgeCount` measuring unordered edges
and `trianglePack.card` measuring edge-disjoint triangles.

The resolution records this statement as true, with stronger ranges and bounds due to
Erdős and Győri. The proof of the general assertion below remains to be formalized. -/
theorem erdos_1009 (c : ℝ) (hc : 0 < c) :
    ∃ f : ℕ, ∀ n k : ℕ, (k : ℝ) < c * n →
      ∀ G : SimpleGraph (Fin n),
        edgeCount G ≥ n ^ 2 / 4 + k →
        ∃ P : Finset (Triple n),
          trianglePack G P ∧ P.card ≥ k - f := by
  sorry Erdos1009
