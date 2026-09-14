/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph on $n$ vertices with chromatic number $\chi(G)$ and let $\sigma(G)$ be the maximal $k$ such that $G$ contains a subdivision of $K_k$. Is it true that\[\chi(G) \ll \frac{n^{1/2}}{\log n}\sigma(G)?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#717 : [ErFa81] [Er81] graph theory Hajós originally conjectured that $\chi(G)\leq \sigma(G)$, which was proved by Dirac [Di52] when $\chi(G)=4$. Catlin [Ca74] disproved Hajós' conjecture for all $\chi(G)\geq 7$, and Erdős and Fajtlowicz [ErFa81] disproved it in a strong form, showing that in fact for almost all graphs on $n$ vertices,\[\chi(G) \gg \frac{n^{1/2}}{\log n}\sigma(G).\]The answer is yes, proved by Fox, Lee, and Sudakov [FLS13] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #717, https://www.erdosproblems.com/717, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos717

/-- Adjacency of consecutive entries in a finite list. -/
def AdjacentList {V : Type*} (G : SimpleGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => G.Adj x y ∧ AdjacentList G (y :: xs)

/-- A simple path from `a` to `b`, represented by its list of internal vertices. -/
def PathIn {V : Type*} (G : SimpleGraph V) (a b : V) (middle : List V) : Prop :=
  (a :: middle ++ [b]).Nodup ∧ AdjacentList G (a :: middle ++ [b])

/-- `ContainsSubdivision G k` means that `G` contains a subdivision of `K_k`.
The branch vertices are represented by an injective map, and for each unordered
pair of branch vertices a simple path is supplied whose internal vertices avoid
all branch vertices and are pairwise disjoint from the internal vertices of
the other paths. -/
def ContainsSubdivision {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (branch : Fin k → Fin n) (middle : Fin k → Fin k → List (Fin n)),
    Function.Injective branch ∧
      (∀ i j, i < j →
        PathIn G (branch i) (branch j) (middle i j) ∧
          (∀ x ∈ middle i j, ∀ t, x ≠ branch t)) ∧
      (∀ i j i' j', i < j → i' < j' →
        (i ≠ i' ∨ j ≠ j') →
        Disjoint (middle i j).toFinset (middle i' j').toFinset)

/-- The chromatic number, defined as the least number of colors admitting a
proper coloring of the vertices of the graph. -/
noncomputable def chromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c : ℕ | ∃ coloring : Fin n → Fin c,
    ∀ ⦃v w⦄, G.Adj v w → coloring v ≠ coloring w}

/-- The subdivision number, defined as the supremum of the orders of complete
graphs whose subdivisions occur in `G`.  The supremum is safe here because the
index set is nonempty and bounded above; the empty-set and unbounded-set junk
values of `sSup` therefore do not arise. -/
noncomputable def subdivisionNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ContainsSubdivision G k}

/-- Every graph contains the empty subdivision. -/
theorem containsSubdivision_zero {n : ℕ} (G : SimpleGraph (Fin n)) :
    ContainsSubdivision G 0 := by
  refine ⟨Fin.elim0, fun i j => [], ?_, ?_, ?_⟩
  · intro i j h
    exact Fin.elim0 i
  · intro i j hij
    exact Fin.elim0 i
  · intro i j i' j' hij hi'j' hne
    simp

/-- The set defining `subdivisionNumber` is nonempty. -/
theorem subdivision_indices_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    ({k : ℕ | ContainsSubdivision G k} : Set ℕ).Nonempty := by
  exact ⟨0, containsSubdivision_zero G⟩

/-- Any subdivision of `K_k` in an `n`-vertex graph has at most `n` branch
vertices, so the set defining `subdivisionNumber` is bounded above. -/
theorem subdivision_indices_bddAbove {n : ℕ} (G : SimpleGraph (Fin n)) :
    BddAbove ({k : ℕ | ContainsSubdivision G k} : Set ℕ) := by
  refine ⟨n, ?_⟩
  intro k hk
  rcases hk with ⟨branch, middle, hbranch, hpaths, hdisjoint⟩
  have hcard : Fintype.card (Fin k) ≤ Fintype.card (Fin n) :=
    Fintype.card_le_of_injective branch hbranch
  simpa using hcard

/-- The identity coloring shows that every graph on `n` vertices is colorable
with `n` colors. -/
theorem colorable_self {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ coloring : Fin n → Fin n,
      ∀ ⦃v w⦄, G.Adj v w → coloring v ≠ coloring w := by
  refine ⟨fun v => v, ?_⟩
  intro v w hadj hEq
  subst w
  exact G.loopless v hadj

/-- The chromatic-number defining set is nonempty, so its `sInf` is not the
empty-set default. -/
theorem chromatic_indices_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    ({c : ℕ | ∃ coloring : Fin n → Fin c,
      ∀ ⦃v w⦄, G.Adj v w → coloring v ≠ coloring w} : Set ℕ).Nonempty := by
  exact ⟨n, colorable_self G⟩

/-- A proved control showing that an edgeless graph admits a one-coloring. -/
theorem colorable_one_of_edgeless {n : ℕ} (G : SimpleGraph (Fin n))
    (hedge : ∀ v w, ¬ G.Adj v w) :
    ∃ coloring : Fin n → Fin 1,
      ∀ ⦃v w⦄, G.Adj v w → coloring v ≠ coloring w := by
  refine ⟨fun _ => 0, ?_⟩
  intro v w hadj
  exact False.elim (hedge v w hadj)

/-- The Fox--Lee--Sudakov bound formalized with the conventional meaning of
`≪`: there are absolute constants `C` and `N` such that the inequality holds
for every graph on `n ≥ N` vertices.

SOURCE-to-statement mapping: the source asks whether
`χ(G) ≪ n^(1/2) / log n * σ(G)`.  Here `G` is a genuine `SimpleGraph`, its
chromatic number is `chromaticNumber G`, and its subdivision parameter is
`subdivisionNumber G`.  The resolution records that the answer is yes, proved
by Fox, Lee, and Sudakov [FLS13].  The proof is not included in the source
entry, so the theorem body remains an explicitly marked gap. -/
theorem fox_lee_sudakov_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        (chromaticNumber G : ℝ) ≤
          C * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)) *
            (subdivisionNumber G : ℝ) := by
  sorry

#print axioms containsSubdivision_zero
#print axioms subdivision_indices_bddAbove
#print axioms colorable_one_of_edgeless

end Erdos717
