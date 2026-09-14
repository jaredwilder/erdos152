/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that the number of graphs on $n$ vertices which do not contain $G$ is\[\leq 2^{(1+o(1))\mathrm{ex}(n;G)}?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#59 : [Er90] [Er93,p.335] [Er97c] [Va99,3.56] graph theory | turan number If $G$ is not bipartite the answer is yes, proved by Erdős, Frankl, and Rödl [EFR86] . The answer is no for $G=C_6$, the cycle on 6 vertices. Morris and Saxton [MoSa16] have proved there are at least\[2^{(1+c)\mathrm{ex}(n;C_6)}\]such graphs for infinitely many $n$, for some constant $c>0$. It is still possible (and conjectured by Morris and Saxton) that the weaker bound of\[2^{O(\mathrm{ex}(n;G))}\]holds for all $G$. In [Va99] the specific case of $G=C_4$ is also asked. Additional thanks to : Tuan Tran Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #59, https://www.erdosproblems.com/59, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research open

namespace ErdosProblem59

/-- A graph on `n` labelled vertices, represented by its set of ordered edges. -/
def GraphOn (n : ℕ) := Finset (Fin n × Fin n)

/-- The edge set is symmetric and contains no loops. -/
def IsSimple {n : ℕ} (g : GraphOn n) : Prop :=
  (∀ u v, (u, v) ∈ g → (v, u) ∈ g) ∧
    (∀ u, (u, u) ∉ g)

/-- `Contains f h` means that `h` contains `f` as a (not necessarily induced)
copy, with the vertices of `f` mapped injectively into those of `h`. -/
def Contains {k n : ℕ} (f : GraphOn k) (h : GraphOn n) : Prop :=
  ∃ φ : Fin k → Fin n,
    Function.Injective φ ∧
      ∀ u v, (u, v) ∈ f → (φ u, φ v) ∈ h

/-- The finite family of simple `n`-vertex graphs avoiding the forbidden graph `f`. -/
noncomputable def avoidingGraphs {k n : ℕ} (f : GraphOn k) : Finset (GraphOn n) := by
  classical
  exact Finset.univ.filter (fun h => IsSimple h ∧ ¬ Contains f h)

/-- The number of graphs on `n` vertices avoiding `f`. -/
noncomputable def avoidCount {k : ℕ} (f : GraphOn k) (n : ℕ) : ℕ :=
  (avoidingGraphs f).card

/-- The number of edges in the represented graph. -/
def edgeCount {n : ℕ} (g : GraphOn n) : ℕ :=
  g.card

/-- The Turán number `ex(n; f)`, defined as the maximum edge count among
simple `n`-vertex graphs avoiding `f`; the empty maximum is `0`. -/
noncomputable def extremal {k : ℕ} (f : GraphOn k) (n : ℕ) : ℕ := by
  classical
  exact (avoidingGraphs f).sup edgeCount

/-- A precise epsilon formulation of the asymptotic upper bound
`2^((1+o(1)) ex(n; f))`. -/
def AsymptoticExponentialBound {k : ℕ} (f : GraphOn k) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log (avoidCount f n : ℝ) ≤
        (1 + ε) * (extremal f n : ℝ) * Real.log 2

/-- The question from the source, read literally as asking whether the
asymptotic exponential bound holds for every finite simple forbidden graph. -/
def Question : Prop :=
  ∀ (k : ℕ) (f : GraphOn k), IsSimple f → AsymptoticExponentialBound f

/-- The weaker conjectural statement recorded in the resolution: the number
of avoiding graphs is bounded by an exponential in the Turán number, with an
arbitrary constant factor in the exponent. -/
def WeakerExponentialBound {k : ℕ} (f : GraphOn k) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.log (avoidCount f n : ℝ) ≤
        C * (extremal f n : ℝ) * Real.log 2

/-- Every graph on zero vertices is the empty edge set.  This is a proved
control exercising the graph representation used in the formalization. -/
theorem graphOn_zero_unique (g : GraphOn 0) : g = ∅ := by
  ext e
  exact Fin.elim0 e.1

#print axioms graphOn_zero_unique

end ErdosProblem59