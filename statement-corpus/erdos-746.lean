/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that, almost surely, a random graph on $n$ vertices with $\geq (\tfrac{1}{2}+\epsilon)n\log n$ edges is Hamiltonian?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#746 : [Er71,p.98] [Er81,p.16] [Er82e,p.69] graph theory A conjecture of Erdős and Rényi [ErRe66] , who proved that almost surely such a graph has a perfect matching (when $n$ is even). This is true. Pósa [Po76] proved that almost surely a random graph with $\geq Cn\log n$ edges is Hamiltonian for some large constant $C$, and Korshunov [Ko77] proved that\[\geq \frac{1}{2}n\log n+\frac{1}{2}n\log\log n+w(n)n\]edges suffices, for any function $w$ which $\to \infty$ as $n \to \infty$. Komlós and Szemerédi [KoSz83] proved the stronger result that with\[\frac{1}{2}n\log n+\frac{1}{2}n\log\log n+cn\]edges the probability that the graph is Hamiltonian tends to $e^{-e^{-2c}}$ as $n \to \infty$. Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 27 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #746, https://www.erdosproblems.com/746, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Can be formalisable JoshuaB Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos746

/-- A Hamilton cycle in a finite simple graph is represented by a cyclic ordering
of all vertices whose consecutive vertices are adjacent. -/
def IsHamiltonian {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → Fin n,
    Function.Bijective f ∧ ∀ i : Fin n, G.Adj (f i) (f (i + 1))

/-- The edge threshold appearing in the question, interpreted over the reals. -/
def EdgeThreshold (ε : ℝ) (n : ℕ) : ℝ :=
  ((1 / 2 : ℝ) + ε) * (n : ℝ) * Real.log (n : ℝ)

/-- The finite sample space used here for the phrase "a random graph with at least
the threshold number of edges": all simple graphs on `Fin n` satisfying the
displayed edge lower bound. -/
def EligibleGraph (ε : ℝ) (n : ℕ) :=
  {G : SimpleGraph (Fin n) //
    EdgeThreshold ε n ≤ (G.edgeSet.ncard : ℝ)}

/-- The Hamiltonian members of the threshold sample space. -/
def HamiltonianEligibleGraph (ε : ℝ) (n : ℕ) :=
  {G : EligibleGraph ε n // IsHamiltonian G.1}

/-- The uniform finite-sample probability of Hamiltonicity.  If the threshold
sample space is empty, this definition returns `0`; the asymptotic claim below
is the non-vacuous mathematical assertion. -/
noncomputable def HamiltonianProbability (ε : ℝ) (n : ℕ) : ℝ :=
  if Fintype.card (EligibleGraph ε n) = 0 then
    0
  else
    (Fintype.card (HamiltonianEligibleGraph ε n) : ℝ) /
      (Fintype.card (EligibleGraph ε n) : ℝ)

/-- A proved control showing that `IsHamiltonian` contains genuine graph
content: the complete graph on three vertices has a Hamilton cycle. -/
theorem complete_triangle_hamiltonian :
    IsHamiltonian (⊤ : SimpleGraph (Fin 3)) := by
  refine ⟨fun i => i, Function.bijective_id, ?_⟩
  intro i
  fin_cases i <;> decide

/-- The source's question, formalized as the asymptotic statement that for
every fixed positive `ε`, the uniform probability of Hamiltonicity among
graphs meeting the edge threshold tends to `1`.

This uses the explicit finite uniform model `EligibleGraph`: the phrase
"random graph ... with at least" is read as uniform sampling from all graphs
satisfying the inequality.  The resolution records that the statement is
true, while the sharper Komlós--Szemerédi limit is not asserted here. -/
def RandomGraphHamiltonicityClaim : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (HamiltonianProbability ε) atTop (𝓝 1)

/-- The resolution of Erdős problem #746: the threshold statement is true.
The proof is left as an explicit gap for the probabilistic random-graph
theorem recorded in the source. -/
theorem random_graph_hamiltonicity (hε : ∀ ε : ℝ, 0 < ε → True) :
    RandomGraphHamiltonicityClaim := by
  sorry

#print axioms complete_triangle_hamiltonian

end Erdos746
