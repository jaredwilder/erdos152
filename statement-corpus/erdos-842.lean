/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex disjoint triangles and adding a Hamiltonian cycle (with all new edges) between these vertices. Does $G$ have chromatic number at most $3$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#842 : [Er92b] graph theory | chromatic number The answer is yes, proved by Fleischner and Stiebitz [FlSt92] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #842, https://www.erdosproblems.com/842, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos842

/-- The graph on `3 * n` vertices consisting of the disjoint triangle edges
and the cyclic Hamiltonian edges. -/
def triangleCycleGraph (n : ℕ) : SimpleGraph (Fin (3 * n)) where
  Adj v w :=
    v ≠ w ∧
      (v.val / 3 = w.val / 3 ∨
        v.val + 1 = w.val ∨
        w.val + 1 = v.val ∨
        (v.val = 0 ∧ w.val + 1 = 3 * n) ∨
        (w.val = 0 ∧ v.val + 1 = 3 * n))
  symm := by
    intro v w h
    simpa [eq_comm, and_comm, or_comm] using h
  loopless := by
    intro v h
    exact h.1 rfl

/-- A proper coloring of a finite graph using the three colors `Fin 3`. -/
def HasColoring3 {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ c : V → Fin 3, ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

/-- POSITIVE WITNESS: the single triangle has a proper coloring with three colors. -/
theorem hasColoring3_witness_pos :
    HasColoring3 (triangleCycleGraph 1) := by
  decide

/-- NEGATIVE WITNESS: the complete graph on four vertices is a near miss
to three-colorability, obtained by adding one vertex to a 3-colorable
complete graph. -/
theorem hasColoring3_witness_neg :
    ¬ HasColoring3 (SimpleGraph.completeGraph (Fin 4)) := by
  decide

/-- The finite, computable test for the source instance at parameter `n`.
It records positivity of `n` and the existence of a proper three-coloring
of the explicitly defined triangle-cycle graph. -/
def finiteInstanceCheck (n : ℕ) : Bool :=
  decide (0 < n ∧ HasColoring3 (triangleCycleGraph n))

/-- POSITIVE WITNESS: the source construction with one triangle passes the
finite instance check. -/
theorem finiteInstanceCheck_witness_pos :
    finiteInstanceCheck 1 = true := by
  decide

/-- NEGATIVE WITNESS: `n = 0` is the near miss obtained by dropping exactly
the positivity condition on the number of triangles. -/
theorem finiteInstanceCheck_witness_neg :
    finiteInstanceCheck 0 = false := by
  decide

/-- The question asks whether every positive instance in the construction
has chromatic number at most three. -/
def Question : Prop :=
  ∀ n : ℕ, 0 < n → HasColoring3 (triangleCycleGraph n)

/-- A bounded decidable version of `Question`, restricted to parameters
`n ≤ N`; the lower bound excludes the degenerate zero-triangle case. -/
def QuestionFinite (N : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → 0 < n → HasColoring3 (triangleCycleGraph n)

/-- POSITIVE WITNESS: the bounded question through one triangle holds. -/
theorem questionFinite_witness_pos :
    QuestionFinite 1 := by
  decide

/-- The published resolution says that the answer is yes, proved by
Fleischner and Stiebitz [FlSt92]. The proof of that theorem is not reproduced
here; this declaration records the resolved mathematical claim. -/
theorem question_resolved : Question := by
  sorry Erdos842

#print axioms Erdos842.hasColoring3_witness_pos
#print axioms Erdos842.hasColoring3_witness_neg
#print axioms Erdos842.finiteInstanceCheck_witness_pos
#print axioms Erdos842.finiteInstanceCheck_witness_neg
#print axioms Erdos842.questionFinite_witness_pos
