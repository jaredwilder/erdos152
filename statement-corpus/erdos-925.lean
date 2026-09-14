/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there a constant $\delta>0$ such that, for all large $n$, if $G$ is a graph on $n$ vertices which is not Ramsey for $K_3$ (i.e. there exists a 2-colouring of the edges of $G$ with no monochromatic triangle) then $G$ contains an independent set of size $\gg n^{1/3+\delta}$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#925 : [Er69b] graph theory | ramsey theory It is easy to show that there exists an independent set of size $\gg n^{1/3}$. In other words, this question asks whether $R(3,3,m) \ll m^{3-c}$ for some $c>0$. This was disproved by Alon and Rödl [AlRo05] , who proved that\[\frac{1}{(\log m)^{4+o(1)}}m^3 \ll R(3,3,m) \ll \frac{\log\log m}{(\log m)^2}m^3.\]As reported in [AlRo05] Sudakov has observed that the $\log\log m$ in the upper bound can be removed. See also [553] . Additional thanks to : Micha Christoph Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #925, https://www.erdosproblems.com/925, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved






open Classical Filter

namespace Erdos925

/-- A two-colouring of the ordered pairs of vertices, with symmetry required on edges
and with no monochromatic triangle. -/
def HasGoodColoring {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Fin n → Bool,
    (∀ a b, G.Adj a b → c a b = c b a) ∧
    (∀ a b d, a ≠ b → a ≠ d → b ≠ d →
      G.Adj a b → G.Adj b d → G.Adj d a →
      ¬(c a b = c b d ∧ c b d = c d a))

/-- POSITIVE WITNESS: the one-vertex empty graph has a two-colouring with no
monochromatic triangle. -/
theorem hasGoodColoring_witness_pos :
    HasGoodColoring (⊥ : SimpleGraph (Fin 1)) := by
  decide

/-- NEGATIVE WITNESS: the complete graph on three vertices has no two-colouring
without a monochromatic triangle. -/
theorem hasGoodColoring_witness_neg :
    ¬ HasGoodColoring (⊤ : SimpleGraph (Fin 3)) := by
  decide

/-- A finite set of vertices is independent in `G`. -/
def IndependentSet {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) : Prop :=
  ∀ ⦃a b : Fin n⦄, a ∈ s → b ∈ s → a ≠ b → ¬ G.Adj a b

/-- POSITIVE WITNESS: the singleton is an independent set in the one-vertex
empty graph. -/
theorem independentSet_witness_pos :
    IndependentSet (⊥ : SimpleGraph (Fin 1)) ({0} : Finset (Fin 1)) := by
  decide

/-- NEGATIVE WITNESS: two vertices are not an independent set in the complete
graph on two vertices. -/
theorem independentSet_witness_neg :
    ¬ IndependentSet (⊤ : SimpleGraph (Fin 2)) ({0, 1} : Finset (Fin 2)) := by
  decide

/-- `HasIndependentSet G k` means that `G` has an independent set of at least
`k` vertices. -/
def HasIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card ≥ k ∧ IndependentSet G s

/-- POSITIVE WITNESS: the one-vertex empty graph has an independent set of
size at least one. -/
theorem hasIndependentSet_witness_pos :
    HasIndependentSet (⊥ : SimpleGraph (Fin 1)) 1 := by
  decide

/-- NEGATIVE WITNESS: the one-vertex empty graph does not have an independent
set of size at least two. -/
theorem hasIndependentSet_witness_neg :
    ¬ HasIndependentSet (⊥ : SimpleGraph (Fin 1)) 2 := by
  decide

/-- `Counterexample G k` records the finite obstruction relevant to the
question: `G` admits a two-colouring with no monochromatic triangle but has no
independent set of size `k`. -/
def Counterexample {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  HasGoodColoring G ∧ ¬ HasIndependentSet G k

/-- POSITIVE WITNESS: the one-vertex empty graph is a counterexample to the
bound `k = 2`. -/
theorem counterexample_witness_pos :
    Counterexample (⊥ : SimpleGraph (Fin 1)) 2 := by
  decide

/-- NEGATIVE WITNESS: lowering the required independent-set size by one removes
the counterexample, while leaving the graph and colouring condition unchanged. -/
theorem counterexample_witness_neg :
    ¬ Counterexample (⊥ : SimpleGraph (Fin 1)) 1 := by
  decide

/-- A bounded decidable analogue of the source question: every good-colourable
graph `G` in this concrete finite instance has an independent set of size at
least `k`. -/
def QuestionFinite {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  HasGoodColoring G → HasIndependentSet G k

/-- POSITIVE WITNESS: the one-vertex empty graph satisfies the bounded
statement at the attainable threshold `k = 1`. -/
theorem questionFinite_witness_pos :
    QuestionFinite (⊥ : SimpleGraph (Fin 1)) 1 := by
  decide

/-- NEGATIVE WITNESS: the near-miss threshold `k = 2` fails for the same graph. -/
theorem questionFinite_witness_neg :
    ¬ QuestionFinite (⊥ : SimpleGraph (Fin 1)) 2 := by
  decide

/-- The source question, with `≫` interpreted in its standard eventual
constant-factor sense. The exponent is written using real powers, and
independent sets are represented by finite subsets of the vertex set. -/
def ErdosQuestion : Prop :=
  ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n), HasGoodColoring G →
        ∃ s : Finset (Fin n),
          IndependentSet G s ∧
          (s.card : ℝ) > C * ((n : ℝ) ^ (1 / 3 + δ))

/-- The resolution recorded by the source says that the eventual strengthened
bound is false. Establishing this requires the Alon--Rödl construction and is
left as an explicit gap rather than asserted as an axiom. -/
theorem erdosQuestion_is_false : ¬ ErdosQuestion := by
  sorry Erdos925
