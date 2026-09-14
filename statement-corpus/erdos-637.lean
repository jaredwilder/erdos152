/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $G$ is a graph on $n$ vertices which contains no complete graph or independent set on $\gg \log n$ vertices then $G$ contains an induced subgraph on $\gg n$ vertices which contains $\gg n^{1/2}$ distinct degrees.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#637 : [Er97d] graph theory | ramsey theory A problem of Erdős, Faudree, and Sós. This was proved by Bukh and Sudakov [BuSu07] . Jenssen, Keevash, Long, and Yepremyan [JKLY20] have proved that there must exist an induced subgraph which contains $\gg n^{2/3}$ distinct degrees (with no restriction on the number of vertices). Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #637, https://www.erdosproblems.com/637, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos637

/-- A finite vertex set whose vertices are pairwise adjacent in `G`. -/
def IsCompleteSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → G.Adj u v

/-- A finite vertex set whose distinct vertices are pairwise nonadjacent in `G`. -/
def IsIndependentSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- `G` contains a complete set of at least `k` vertices. -/
def ContainsCompleteAtLeast {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, k ≤ S.card ∧ IsCompleteSet G S

/-- `G` contains an independent set of at least `k` vertices. -/
def ContainsIndependentAtLeast {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, k ≤ S.card ∧ IsIndependentSet G S

/-- The number of distinct degrees in the induced subgraph of `G` on `S`. -/
noncomputable def distinctDegrees {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (S.image (fun v =>
    (G.induce (S : Set V)).degree
      ⟨v, by
        simpa only [Set.mem_coe] using v.property⟩)).card

/-- 
The hypothesis in the Erdős problem, using the discrete logarithm
`Nat.log 2 n` to represent `log n`: there are no complete or independent
sets of size at least the indicated threshold.
-/
def RamseySparseAt {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a : ℝ) : Prop :=
  ¬ ContainsCompleteAtLeast G
      (Nat.floor (a * (Nat.log 2 (Fintype.card V) : ℝ))) ∧
  ¬ ContainsIndependentAtLeast G
      (Nat.floor (a * (Nat.log 2 (Fintype.card V) : ℝ)))

/-- 
The conclusion that an induced subgraph has linearly many vertices and
`n^(1/2)`-many distinct degrees.
-/
def HasLargeDegreeInducedSubgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (b d : ℝ) : Prop :=
  ∃ S : Finset V,
    b * (Fintype.card V : ℝ) ≤ S.card ∧
    d * Real.sqrt (Fintype.card V : ℝ) ≤ distinctDegrees G S

/-- 
The source says: “If `G` has no complete graph or independent set on
`≫ log n` vertices, then `G` has an induced subgraph on `≫ n` vertices
with `≫ n^{1/2}` distinct degrees.”  Here each `≫` is represented by an
absolute positive real constant, and the statement is required only
beyond an absolute finite-size threshold.  The resolution records this
result as proved by Bukh and Sudakov; the stronger `n^(2/3)` result of
Jenssen, Keevash, Long, and Yepremyan is not formalized here. -/
theorem erdos_637 :
    ∃ a b d : ℝ, 0 < a ∧ 0 < b ∧ 0 < d ∧
      ∃ N : ℕ, ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        N ≤ Fintype.card V →
        RamseySparseAt G a →
        HasLargeDegreeInducedSubgraph G b d := by
  sorry

/-- The degree-value set of the empty induced subgraph is empty. -/
theorem distinctDegrees_empty {V : Type*} [Fintype V]
    (G : SimpleGraph V) : distinctDegrees G ∅ = 0 := by
  simp [distinctDegrees]

/-- Every graph contains a complete set of at least zero vertices. -/
theorem containsCompleteAtLeast_zero {V : Type*}
    (G : SimpleGraph V) : ContainsCompleteAtLeast G 0 := by
  refine ⟨∅, by simp, ?_⟩
  intro u v hu hv huv
  simp at hu

/-- Every graph contains an independent set of at least zero vertices. -/
theorem containsIndependentAtLeast_zero {V : Type*}
    (G : SimpleGraph V) : ContainsIndependentAtLeast G 0 := by
  refine ⟨∅, by simp, ?_⟩
  intro u v hu hv huv
  simp at hu

#print axioms distinctDegrees_empty
#print axioms containsCompleteAtLeast_zero
#print axioms containsIndependentAtLeast_zero

end Erdos637
