/- 
SOURCE (frozen), NODE n000-question (question), VERBATIM:
There is a function $f:(1/2,\infty)\to \mathbb{R}$ such that $f(c)\to 0$ as $c\to 1/2$ and $f(c)\to 1$ as $c\to \infty$ and every random graph with $n$ vertices and $cn$ edges has (with high probability) a path of length at least $f(c)n$.

SOURCE (frozen), NODE n001-resolution (resolution), VERBATIM:
#900 : \cite[{Er78,p.32} [Er82e] graph theory This was proved by Ajtai, Komlós, and Szemerédi [AKS81] . Curiously, in [Er78] Erdős wrote 'I conjectured [the above]...Szemerédi disagrees; he believes that for every $c$ the longest path is almost surely $o(n)$. At present we can not decide who is right.' Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 07 March 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #900, https://www.erdosproblems.com/900, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter
open Topology

-- @category research solved





open Classical Filter

namespace Erdos900

/-- A graph has a simple path of length `k` when it has an injective vertex
sequence of length `k + 1` whose consecutive vertices are adjacent. -/
def HasPathLength {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ v : Fin (k + 1) → Fin n,
    Function.Injective v ∧
      ∀ i : Fin k, G.Adj (v i.castSucc) (v i.succ)

/-- The number of edges of a finite simple graph. -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

/-- The integer number of edges represented by the real quantity `c * n`,
using the nonnegative integer part. -/
noncomputable def edgeNumber (c : ℝ) (n : ℕ) : ℕ :=
  Int.toNat ⌊c * (n : ℝ)⌋

/-- Uniform probability of a predicate on the finite set of simple graphs on
`Fin n`. The denominator is nonzero because the universal finite set of graphs
is nonempty; thus this is an actual finite uniform probability, not a default
value arising from an empty or unbounded supremum or infimum. -/
noncomputable def uniformGraphProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Finset.univ.filter P).card / Finset.univ.card

/-- The event that a graph has the prescribed rounded edge count and a path
whose length is at least `f(c) * n`. -/
def linearPathEvent (f : ℝ → ℝ) (c : ℝ) (n : ℕ)
    (G : SimpleGraph (Fin n)) : Prop :=
  edgeCount G = edgeNumber c n ∧
    ∃ k : ℕ, HasPathLength G k ∧ (k : ℝ) ≥ f c * (n : ℝ)

/-- A direct formalization of the source statement: there is a function with
the two endpoint limits such that, for every `c > 1/2`, the uniform probability
of the corresponding finite random-graph event tends to one.

The phrase “with high probability” is formalized as convergence of the finite
uniform probabilities to `1`, and `cn` edges is rounded down to an integer
because a finite graph has an integer edge count. The source records this result
as proved by Ajtai, Komlós, and Szemerédi; the remaining gap here is the proof
of the probabilistic theorem itself. -/
theorem erdos900 :
    ∃ f : ℝ → ℝ,
      (Tendsto f (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2 : ℝ))) (𝓝 0)) ∧
      (Tendsto f atTop (𝓝 1)) ∧
      ∀ c : ℝ, c > 1 / 2 →
        Tendsto
          (fun n : ℕ =>
            uniformGraphProbability n
              (fun G => linearPathEvent f c n G))
          atTop (𝓝 1) := by
  sorry

/-- Bounded decidable control predicate: on a concrete finite graph, the
predicate records the existence of a path of the specified finite length. -/
def FinitePathInstance (n k : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  HasPathLength G k

/-- POSITIVE WITNESS: the complete graph on two vertices has a path of length
one. This is a concrete finite instance satisfying `FinitePathInstance`. -/
theorem finitePathInstance_witness_pos :
    FinitePathInstance 2 1 (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨id, Function.injective_id, ?_⟩
  intro i
  fin_cases i
  simp

/-- NEGATIVE WITNESS: the empty graph on two vertices is the near-miss obtained
from the positive instance by deleting its sole edge, so it has no path of
length one. -/
theorem finitePathInstance_witness_neg :
    ¬ FinitePathInstance 2 1 (⊥ : SimpleGraph (Fin 2)) := by
  intro h
  rcases h with ⟨v, hv, hadj⟩
  have h0 := hadj ⟨0, by omega⟩
  simp at h0

#print axioms finitePathInstance_witness_pos
#print axioms finitePathInstance_witness_neg

end Erdos900
