/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $t<\lfloor n/2\rfloor$. Does every graph on $n$ vertices with $\lfloor n^2/4\rfloor+t$ edges contain at least $t\lfloor n/2\rfloor$ triangles?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#1010 : [Er62d] graph theory Rademacher proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+1$ edges contains at least $\lfloor n/2\rfloor$ triangles. Erdős [Er62d] proved that every graph on $n$ vertices with $\lfloor n^2/4\rfloor+t$ edges contains at least $t\lfloor n/2\rfloor$ triangles, for all $t<cn$, for some constant $c>0$. This is true, and was proved independently by Lovász and Simonovits [LoSi76] and Nikiforov and Khadzhiivanov [NiKh81] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #1010, https://www.erdosproblems.com/1010, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




-- @category research solved








import Mathlib
open Classical Filter

namespace Erdos1010

/-- A finite graph on `n` labelled vertices, represented by its Boolean adjacency matrix. -/
def BoolGraph (n : ℕ) := Fin n → Fin n → Bool

/-- `IsSimpleGraph G` says that `G` has no loops and has symmetric adjacency. -/
def IsSimpleGraph {n : ℕ} (G : BoolGraph n) : Prop :=
  (∀ v, G v v = false) ∧ ∀ u v, G u v = G v u

/-- The number of edges of a finite Boolean graph, counting each unordered edge once. -/
def edgeCount {n : ℕ} (G : BoolGraph n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G p.1 p.2 = true)).card

/-- The number of triangles of a finite Boolean graph, counting increasing vertex triples. -/
def triangleCount {n : ℕ} (G : BoolGraph n) : ℕ :=
  (((Finset.univ.product Finset.univ).product Finset.univ).filter
    (fun p : (Fin n × Fin n) × Fin n =>
      p.1.1 < p.1.2 ∧ p.1.2 < p.2 ∧
      G p.1.1 p.1.2 = true ∧
      G p.1.1 p.2 = true ∧
      G p.1.2 p.2 = true)).card

/-- The finite, decidable form of the question: for every simple graph on `n`
vertices, `t < floor(n/2)` and the prescribed edge count imply the prescribed
triangle lower bound. -/
def Question1010 (n t : ℕ) : Prop :=
  t < n / 2 ∧
    ∀ G : BoolGraph n, IsSimpleGraph G →
      edgeCount G = n ^ 2 / 4 + t →
      t * (n / 2) ≤ triangleCount G

/-- POSITIVE WITNESS: at `n = 2` and `t = 0`, the finite question holds. -/
theorem Question1010_witness_pos : Question1010 2 0 := by
  decide

/-- NEGATIVE WITNESS: `n = 2`, `t = 1` is a near miss obtained by violating
exactly the strict hypothesis `t < floor(n/2)`. -/
theorem Question1010_witness_neg : ¬ Question1010 2 1 := by
  decide

/-- POSITIVE WITNESS: the empty Boolean graph is simple. -/
theorem IsSimpleGraph_witness_pos :
    IsSimpleGraph (fun _ _ : Fin 2 => false) := by
  decide

/-- NEGATIVE WITNESS: changing exactly one loop entry of the empty graph to
`true` violates simplicity. -/
theorem IsSimpleGraph_witness_neg :
    ¬ IsSimpleGraph (fun u v : Fin 2 => decide (u = 0 ∧ v = 0)) := by
  decide

/-- A concrete control showing that the edge-count definition computes the
empty graph correctly. -/
theorem edgeCount_empty :
    edgeCount (fun _ _ : Fin 3 => false) = 0 := by
  decide

/-- A concrete control showing that the triangle-count definition computes one
triangle in the complete graph on three vertices. -/
theorem triangleCount_complete_three :
    triangleCount (fun _ _ : Fin 3 => true) = 1 := by
  decide

/-- The source's resolved quantitative statement: there is a positive constant
`c` such that, for every natural `n` and `t` with `t < c n`, every simple graph
with `floor(n^2/4)+t` edges has at least `t floor(n/2)` triangles. The proof
of this literature theorem remains an explicit gap. -/
theorem resolution1010 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n t : ℕ, (t : ℝ) < c * n →
        ∀ G : BoolGraph n, IsSimpleGraph G →
          edgeCount G = n ^ 2 / 4 + t →
          t * (n / 2) ≤ triangleCount G := by
  sorry

#print axioms Question1010_witness_pos
#print axioms Question1010_witness_neg
#print axioms IsSimpleGraph_witness_pos
#print axioms IsSimpleGraph_witness_neg
#print axioms edgeCount_empty
#print axioms triangleCount_complete_three

end Erdos1010
