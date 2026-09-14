/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there a set $A\subset \mathbb{N}$ of density $0$ and a constant $c>0$ such that every graph on sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is in $A$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#72 : [Er94b] [Er95] [Er97b] [Er97c] graph theory | cycles Bollobás [Bo77] proved that such a $c$ does exist if $A$ is an infinite arithmetic progression containing even numbers (see [71] ). Erdős was 'almost certain' that if $A$ is the set of powers of $2$ then no such $c$ exists (although he conjectured that $n$ vertices and average degree $\gg (\log n)^{C}$ suffices for some $C=O(1)$). If $A$ is the set of squares (or the set of $p\pm 1$ for $p$ prime) then he had no guess. Solved by Verstraëte [Ve05] , who gave a non-constructive proof that such a set $A$ exists. Liu and Montgomery [LiMo20] proved that in fact this is true when $A$ is the set of powers of $2$ (more generally any set of even numbers which doesn't grow too quickly) - in particular this contradicts the previous belief of Erdős. See also the entry in the graphs problem collection . Additional thanks to : Richard Montgomery Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #72, https://www.erdosproblems.com/72, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/
import Mathlib

-- @category research solved

namespace Erdos72

open scoped BigOperators

/-- A finite simple graph on the vertex set `Fin n`. -/
structure Graph72 (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ ⦃u v : Fin n⦄, adj u v → adj v u
  loopless : ∀ u : Fin n, ¬ adj u u

/-- The degree of a vertex in a finite simple graph. -/
noncomputable def degree72 {n : ℕ} (G : Graph72 n) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.adj v w)).card

/-- The average degree of a finite simple graph, regarded as a real number. -/
noncomputable def averageDegree72 {n : ℕ} (G : Graph72 n) : ℝ :=
  (∑ v : Fin n, (degree72 G v : ℝ)) / (n : ℝ)

/-- The successor of a cyclic index in `Fin k`, for positive `k`. -/
def nextFin72 {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- The graph contains a simple cycle of the specified length. -/
def HasCycleLength72 {n : ℕ} (G : Graph72 n) (k : ℕ) : Prop :=
  ∃ hk : 0 < k,
    ∃ v : Fin k → Fin n,
      Function.Injective v ∧
        ∀ i : Fin k, G.adj (v i) (v (nextFin72 hk i))

/-- A set of natural numbers has density zero, expressed through eventual finite counting bounds. -/
noncomputable def DensityZero72 (A : Set ℕ) : Prop := by
  classical
  exact
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ((Finset.filter (fun m => m ∈ A) (Finset.range n)).card : ℝ) ≤ ε * (n : ℝ)

/-- The property that `A` supplies an eventual positive average-degree cycle threshold. -/
def GoodCycleSet72 (A : Set ℕ) (c : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ G : Graph72 n, c ≤ averageDegree72 G →
      ∃ k : ℕ, 3 ≤ k ∧ k ∈ A ∧ HasCycleLength72 G k

/-- The formalized existence statement corresponding to Erdős Problem #72. -/
def Question72 : Prop :=
  ∃ A : Set ℕ, ∃ c : ℝ, DensityZero72 A ∧ 0 < c ∧ GoodCycleSet72 A c

/-- The empty set satisfies the formal density-zero predicate, providing a proved control for the definitions. -/
theorem empty_densityZero72 : DensityZero72 (∅ : Set ℕ) := by
  classical
  intro ε hε
  refine ⟨1, ?_⟩
  intro n hn
  have hnonneg : 0 ≤ ε * (n : ℝ) :=
    mul_nonneg (le_of_lt hε) (by positivity)
  simpa using hnonneg

#print axioms empty_densityZero72

end Erdos72