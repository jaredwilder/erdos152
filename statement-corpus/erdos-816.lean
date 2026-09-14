/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph with $2n+1$ vertices and $n^2+n+1$ edges. Must $G$ contain two vertices of the same degree which are joined by a path of length $3$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#816 : [Er91] graph theory A problem of Erdős and Hajnal. The example of $K_{n,n+1}$ shows that this fails if we only have $n^2+n$ edges. This is true, and was proved by Chen and Ma [ChMa25] , who prove the stronger statement that, provided $n\geq 600$, all graphs with $2n+1$ vertices and at least $n^2+n$ edges contain two vertices of the same degree joined by a path of length $3$, except $K_{n,n+1}$. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #816, https://www.erdosproblems.com/816, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Looks tractable None Looks tractable None Looks tractable JoshuaB Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos816

/-- The number of unordered edges represented by a finite Boolean adjacency table. -/
def finiteEdgeCount (n : ℕ) (A : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n =>
    p.1.val < p.2.val ∧ A p.1 p.2 = true).card

/-- The degree of a vertex in a finite Boolean adjacency table. -/
def finiteDegree (n : ℕ) (A : Fin n → Fin n → Bool) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w : Fin n => A v w = true).card

/-- A bounded, decidable version of the Erdős 816 assertion for a finite adjacency table. -/
def questionFinite (n : ℕ) (A : Fin n → Fin n → Bool) : Bool :=
  decide (
    (∀ i j, i ≠ j → A i j = A j i) ∧
    (∀ i, A i i = false) ∧
    finiteEdgeCount (2 * n + 1) A = n * n + n + 1 ∧
    ∃ u v a b : Fin (2 * n + 1),
      u ≠ v ∧
      u ≠ a ∧
      u ≠ b ∧
      v ≠ a ∧
      v ≠ b ∧
      a ≠ b ∧
      finiteDegree (2 * n + 1) A u = finiteDegree (2 * n + 1) A v ∧
      A u a = true ∧
      A a b = true ∧
      A b v = true
  )

/-- A concrete five-vertex adjacency table with seven edges and a length-three path
whose endpoints have equal degree. -/
def positiveTable : Fin 5 → Fin 5 → Bool :=
  fun i j => decide (
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0) ∨
    (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
    (i.val = 1 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 2)
  )

/-- A near-miss of `positiveTable`, obtained by deleting exactly the edge `{2,4}`. -/
def negativeTable : Fin 5 → Fin 5 → Bool :=
  fun i j => decide (
    (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨
    (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
    (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
    (i.val = 0 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 0) ∨
    (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
    (i.val = 1 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 1)
  )

/-- POSITIVE WITNESS: the seven-edge table on five vertices satisfies the bounded assertion. -/
theorem questionFinite_witness_pos :
    questionFinite 2 positiveTable = true := by
  decide

/-- NEGATIVE WITNESS: deleting exactly one edge from the positive table makes its edge
count miss the required value, while leaving the displayed path and equal-degree endpoints. -/
theorem questionFinite_witness_neg :
    questionFinite 2 negativeTable = false := by
  decide

/-- The source's assertion for a graph: the first argument is the graph under discussion,
and the existentially quantified vertices are required to be distinct endpoints and
internal vertices of a path of length three. The source clause
"there exist two vertices of the same degree which are joined by a path of length 3"
is read literally as a three-edge path `u--a--b--v`. The resolution records this as true;
the proof is not reproduced here. -/
theorem erdos_816 :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin (2 * n + 1)),
      (Finset.univ.filter fun p : Fin (2 * n + 1) × Fin (2 * n + 1) =>
        p.1.val < p.2.val ∧ G.Adj p.1 p.2).card = n * n + n + 1 →
      ∃ u v a b : Fin (2 * n + 1),
        u ≠ v ∧
        u ≠ a ∧
        u ≠ b ∧
        v ≠ a ∧
        v ≠ b ∧
        a ≠ b ∧
        G.neighborSet u |>.toFinset.card = G.neighborSet v |>.toFinset.card ∧
        G.Adj u a ∧
        G.Adj a b ∧
        G.Adj b v := by
  sorry Erdos816
