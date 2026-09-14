/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $G$ is a graph on $n$ vertices which has no two adjacent vertices of degree $\geq 3$ then\[R(G)\ll n,\]where the implied constant is absolute.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#800 : [BuEr75] graph theory | ramsey theory A problem of Burr and Erdős. Solved in the affirmative by Alon [Al94] . This is a special case of [163] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #800, https://www.erdosproblems.com/800, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/

-- @category research solved





import Mathlib
open Classical







open Classical Filter

namespace Erdos800

/-- A finite graph has the source's required degree condition: adjacent vertices
do not both have degree at least three. -/
def GoodGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, G.Adj u v →
    G.degree u < 3 ∨ G.degree v < 3

/-- POSITIVE WITNESS: the empty graph on four vertices satisfies the degree condition. -/
theorem GoodGraph_witness_pos :
    GoodGraph (⊥ : SimpleGraph (Fin 4)) := by
  simp [GoodGraph]

/-- NEGATIVE WITNESS: the complete graph on four vertices is a near-miss,
because adjacent vertices have degree three. -/
theorem GoodGraph_witness_neg :
    ¬ GoodGraph (⊤ : SimpleGraph (Fin 4)) := by
  simp [GoodGraph]

/-- A bounded, computable version of the degree condition for finite Boolean
adjacency tables. This is used only as a decidable finite control. -/
def GoodGraphFinite (n : ℕ) (a : Fin n → Fin n → Bool) : Prop :=
  ∀ u v : Fin n, a u v = true →
    (Finset.univ.filter (fun w => a u w = true)).card < 3 ∨
      (Finset.univ.filter (fun w => a v w = true)).card < 3

/-- POSITIVE WITNESS: the all-zero adjacency table satisfies the bounded condition. -/
theorem GoodGraphFinite_witness_pos :
    GoodGraphFinite 4 (fun _ _ : Fin 4 => false) := by
  decide

/-- NEGATIVE WITNESS: the all-one adjacency table is a near-miss obtained by
allowing one adjacent pair of vertices to have degree at least three. -/
theorem GoodGraphFinite_witness_neg :
    ¬ GoodGraphFinite 4 (fun _ _ : Fin 4 => true) := by
  decide

/-- `HasMonochromaticCopy G c N` means that the two-colouring `c` of ordered
pairs of vertices of `Fin N` contains a monochromatic copy of every edge of
`G`, witnessed by an injective map. -/
def HasMonochromaticCopy {n N : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin N → Fin N → Bool) : Prop :=
  ∃ f : Fin n → Fin N, Function.Injective f ∧
    ∃ b : Bool, ∀ ⦃u v : Fin n⦄, G.Adj u v → c (f u) (f v) = b

/-- The Ramsey number used here is the least order at which every Boolean
colouring contains a monochromatic copy of the graph. The `sInf` is an
infimum over a nonempty set; the separate nonemptiness control below records
the fact that its default value on an empty set is not being used. -/
noncomputable def RamseyNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {N : ℕ | ∀ c : Fin N → Fin N → Bool, HasMonochromaticCopy G c}

/-- The set defining `RamseyNumber G` is nonempty. This is the finite Ramsey
existence input; proving it from first principles is not included here. -/
theorem ramseyNumber_admissible_nonempty {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    Set.Nonempty {N : ℕ | ∀ c : Fin N → Fin N → Bool, HasMonochromaticCopy G c} := by
  sorry

/-- The defining set for `RamseyNumber` is bounded below by zero. -/
theorem ramseyNumber_admissible_bddBelow {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    BddBelow {N : ℕ | ∀ c : Fin N → Fin N → Bool, HasMonochromaticCopy G c} := by
  refine ⟨0, ?_⟩
  intro N hN
  exact Nat.zero_le N

/-- Burr--Erdős' theorem for Problem #800. The source clause
"If G is a graph on n vertices ... then R(G) << n" is read as the existence
of one absolute constant `C` such that every finite graph satisfying
`GoodGraph` has `RamseyNumber G ≤ C * n`. The resolution node records this
claim as solved by Alon. The proof remains an explicit formalization gap. -/
theorem burr_erdos :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      GoodGraph G → RamseyNumber G ≤ C * n := by
  sorry

#print axioms GoodGraph_witness_pos
#print axioms GoodGraph_witness_neg
#print axioms GoodGraphFinite_witness_pos
#print axioms GoodGraphFinite_witness_neg
#print axioms ramseyNumber_admissible_bddBelow

end Erdos800
