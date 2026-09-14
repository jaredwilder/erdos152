/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
If $G$ is a graph which contains odd cycles of $\leq k$ different lengths then $\chi(G)\leq 2k+2$, with equality if and only if $G$ contains $K_{2k+2}$.
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#58 : [Er90] graph theory | chromatic number | cycles Conjectured by Bollobás and Erdős. Bollobás and Shelah have confirmed this for $k=1$. Proved by Gyárfás [Gy92] , who proved the stronger result that, if $G$ is 2-connected, then $G$ is either $K_{2k+2}$ or contains a vertex of degree at most $2k$. A stronger form was established by Gao, Huo, and Ma [GaHuMa21] , who proved that if a graph $G$ has chromatic number $\chi(G)\geq 2k+3$ then $G$ contains cycles of $k+1$ consecutive odd lengths. Additional thanks to : David Penman Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #58, https://www.erdosproblems.com/58, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem58

/-- A finite simple graph on `Fin n`, represented by its adjacency relation. -/
structure EGraph (n : Nat) where
  edge : Fin n → Fin n → Prop
  symmetric : ∀ ⦃u v : Fin n⦄, edge u v → edge v u
  loopless : ∀ u : Fin n, ¬ edge u u

/-- The cyclic successor of an index in a nonempty finite cyclic ordering. -/
def nextIndex (l : Nat) (hl : 0 < l) (i : Fin l) : Fin l :=
  ⟨(i.val + 1) % l, Nat.mod_lt _ hl⟩

/-- `IsOddCycleLength G l` says that `G` contains a simple cycle of odd length `l`. -/
def IsOddCycleLength {n : Nat} (G : EGraph n) (l : Nat) : Prop :=
  l % 2 = 1 ∧
    ∃ hl : 3 ≤ l, ∃ f : Fin l → Fin n,
      Function.Injective f ∧
        ∀ i : Fin l, G.edge (f i) (f (nextIndex l (by omega) i))

/-- The finite set of odd cycle lengths of a finite graph. -/
noncomputable def oddCycleLengths {n : Nat} (G : EGraph n) : Finset Nat :=
  (Finset.range (n + 1)).filter (IsOddCycleLength G)

/-- A proper coloring of `G` using colors indexed by `Fin c`. -/
def ChromaticAtMost {n : Nat} (G : EGraph n) (c : Nat) : Prop :=
  ∃ f : Fin n → Fin c, ∀ ⦃u v : Fin n⦄, G.edge u v → f u ≠ f v

/-- The chromatic number of a finite graph, defined as the least number of colors. -/
noncomputable def chromaticNumber {n : Nat} (G : EGraph n) : Nat :=
  sInf {c : Nat | ChromaticAtMost G c}

/-- `ContainsClique G m` says that `G` contains a copy of the complete graph `K_m`. -/
def ContainsClique {n : Nat} (G : EGraph n) (m : Nat) : Prop :=
  ∃ f : Fin m → Fin n,
    Function.Injective f ∧
      ∀ ⦃u v : Fin m⦄, u ≠ v → G.edge (f u) (f v)

/-- The literal formalization of Erdos Problem 58.

SOURCE mapping: the phrase “If `G` is a graph which contains odd cycles of at most `k`
different lengths” is represented by
`(oddCycleLengths G).card ≤ k`; the conclusion `χ(G) ≤ 2k+2` is
`chromaticNumber G ≤ 2 * k + 2`; and “`G` contains `K_{2k+2}`” is
`ContainsClique G (2 * k + 2)`. The resolution records this claim as proved. -/
def ErdosClaim : Prop :=
  ∀ (n k : Nat) (G : EGraph n),
    (oddCycleLengths G).card ≤ k →
      chromaticNumber G ≤ 2 * k + 2 ∧
        (chromaticNumber G = 2 * k + 2 ↔ ContainsClique G (2 * k + 2))

/-- Every finite graph can be colored using one distinct color for each vertex. -/
theorem coloring_by_vertices {n : Nat} (G : EGraph n) :
    ChromaticAtMost G n := by
  refine ⟨id, ?_⟩
  intro u v huv h
  subst v
  exact G.loopless u huv

/-- Every nonempty finite graph contains a copy of `K₁`. -/
theorem containsClique_one {n : Nat} (G : EGraph n) (hn : 0 < n) :
    ContainsClique G 1 := by
  let v : Fin n := ⟨0, hn⟩
  refine ⟨fun _ => v, ?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim _ _
  · intro a b hab
    exfalso
    exact hab (Subsingleton.elim _ _)

#print axioms coloring_by_vertices
#print axioms containsClique_one

end ErdosProblem58