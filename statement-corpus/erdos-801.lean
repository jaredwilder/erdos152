/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $G$ is a graph on $n$ vertices containing no independent set on $>n^{1/2}$ vertices then there is a set of $\leq n^{1/2}$ vertices containing $\gg n^{1/2}\log n$ edges.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#801 : [Er79g] graph theory | ramsey theory Proved by Alon [Al96b] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #801, https://www.erdosproblems.com/801, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical
open scoped BigOperators

-- @category research solved






open Classical Filter

namespace Erdos801

/-- An independent set in `G` is a finite set whose distinct vertices have no edge between them. -/
def IndependentOn {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : Prop :=
  s.Pairwise (fun x y => ¬ G.Adj x y)

/-- The graph has no independent set larger than the square root threshold. -/
def NoLargeIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n), IndependentOn G s → s.card ≤ Nat.sqrt n

/-- The number of unoriented edges induced by a finite vertex set. -/
def InducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : ℕ :=
  (∑ x ∈ s, (s.filter (fun y => G.Adj x y)).card) / 2

/-- A bounded, decidable rendering of the conclusion, using `1/100` as a
concrete positive interpretation of the source's `≫` constant. The floor is
represented by natural-number division. -/
def HasSmallDenseSet {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ s : Finset (Fin n),
    s.card ≤ Nat.sqrt n ∧
      InducedEdgeCount G s ≥ Nat.sqrt n * Nat.log n / 100

/-- The finite-instance predicate corresponding to the source statement. -/
def QuestionFinite (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  NoLargeIndependentSet G ∧ HasSmallDenseSet G

/-- POSITIVE WITNESS: the complete graph on two vertices satisfies the finite predicate. -/
theorem questionFinite_witness_pos :
    QuestionFinite 2 (⊤ : SimpleGraph (Fin 2)) := by
  decide

/-- NEGATIVE WITNESS: deleting the sole edge from the positive witness creates an
independent set of size two, violating exactly the first condition. -/
theorem questionFinite_witness_neg :
    ¬ QuestionFinite 2 (⊥ : SimpleGraph (Fin 2)) := by
  decide

/-- The formalized Erdos problem: every finite graph with no independent set larger
than `sqrt n` has a set of at most `sqrt n` vertices spanning at least a fixed
positive constant times `sqrt n * log n` edges, here represented by the explicit
constant `1/100`. The source says this result was proved by Alon; the proof is
not reproduced in this file. -/
def Erdos801Claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    NoLargeIndependentSet G → HasSmallDenseSet G

/-- The source clause reads: “If `G` ... containing no independent set ... then
there is a set ... containing ... edges.” Thus the same graph `G` is the host
graph in both predicates, and the selected finite set is the small vertex set
whose induced edges are counted. The mathematical proof of the recorded result
remains to be supplied. -/
theorem erdos801 : Erdos801Claim := by
  sorry Erdos801
