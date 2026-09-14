/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $k\geq 4$ and let $f_k(n)$ be the largest $m$ such that there is a graph on $n$ vertices with chromatic number $k$ in which every odd cycle has length $> m$. Is it true that\[f_k(n) \asymp n^{\frac{1}{k-2}}?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#921 : [Er69b] graph theory | chromatic number | cycles A question of Erdős and Gallai. Gallai [Ga63] proved that\[f_4(n) \gg n^{1/2}\]and Erdős (unpublished) proved $f_4(n) \ll n^{1/2}$. This was proved for all $k\geq 4$ by Kierstead, Szemerédi, and Trotter [KST84] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #921, https://www.erdosproblems.com/921, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/





import Mathlib
open Classical
open Filter

-- @category research solved





open Classical Filter

namespace Erdos921

/-- A proper coloring of a finite simple graph by `k` colors. -/
def ProperColoring {n k : ℕ} (G : SimpleGraph (Fin n))
    (c : Fin n → Fin k) : Prop :=
  ∀ ⦃u v : Fin n⦄, G.Adj u v → c u ≠ c v

/-- POSITIVE WITNESS: the identity coloring properly colors the complete graph on four vertices with four colors. -/
theorem ProperColoring_witness_pos :
    ProperColoring (⊤ : SimpleGraph (Fin 4)) (fun i : Fin 4 => i) := by
  decide

/-- NEGATIVE WITNESS: the constant coloring is a near-miss that fails properness on one edge. -/
theorem ProperColoring_witness_neg :
    ¬ ProperColoring (⊤ : SimpleGraph (Fin 4)) (fun _ : Fin 4 => (0 : Fin 4)) := by
  decide

/-- A graph has chromatic number exactly `k`, expressed by existence of a proper `k`-coloring
and nonexistence of a proper `(k-1)`-coloring. -/
def ExactChromatic {n k : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∃ c : Fin n → Fin k, ProperColoring G c) ∧
    ¬ ∃ c : Fin n → Fin (k - 1), ProperColoring G c

/-- POSITIVE WITNESS: the complete graph on four vertices has chromatic number four. -/
theorem ExactChromatic_witness_pos :
    ExactChromatic (⊤ : SimpleGraph (Fin 4)) 4 := by
  decide

/-- NEGATIVE WITNESS: lowering the claimed chromatic number from four to three is a near miss. -/
theorem ExactChromatic_witness_neg :
    ¬ ExactChromatic (⊤ : SimpleGraph (Fin 4)) 3 := by
  decide

/-- The edges of a cyclic walk through `v : Fin l → Fin n`, with the final vertex
joined back to the first. -/
def CycleEdges {n : ℕ} (G : SimpleGraph (Fin n)) (l : ℕ) (hl : 0 < l)
    (v : Fin l → Fin n) : Prop :=
  ∀ i : Fin l,
    G.Adj (v i) (v ⟨(i.val + 1) % l, Nat.mod_lt _ hl⟩)

/-- POSITIVE WITNESS: the identity parametrizes a triangle in the complete graph. -/
theorem CycleEdges_witness_pos :
    CycleEdges (⊤ : SimpleGraph (Fin 4)) 3 (by decide) (fun i : Fin 3 => (i : Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: replacing the complete graph by the empty graph breaks exactly the
required cyclic adjacency. -/
theorem CycleEdges_witness_neg :
    ¬ CycleEdges (⊥ : SimpleGraph (Fin 4)) 3 (by decide) (fun i : Fin 3 => (i : Fin 4)) := by
  decide

/-- Every simple odd cycle in a graph on `n` vertices has length greater than `m`.
The finite interval `3 ≤ l ≤ n` is sufficient because a simple cycle cannot have more
than `n` vertices. -/
def AllOddCyclesLong {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∀ l ∈ Finset.Icc 3 n, ∀ hl : Odd l, ∀ v : Fin l → Fin n,
    Function.Injective v → CycleEdges G l (by omega) v → m < l

/-- POSITIVE WITNESS: every odd simple cycle in `K₄` has length greater than two. -/
theorem AllOddCyclesLong_witness_pos :
    AllOddCyclesLong (⊤ : SimpleGraph (Fin 4)) 2 := by
  decide

/-- NEGATIVE WITNESS: increasing the bound by one is a near miss, refuted by a triangle. -/
theorem AllOddCyclesLong_witness_neg :
    ¬ AllOddCyclesLong (⊤ : SimpleGraph (Fin 4)) 3 := by
  decide

/-- The finite-instance predicate expressing the source's graph condition: the graph has
chromatic number `k` and all its odd cycles have length greater than `m`. -/
def GoodBound (k n m : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  4 ≤ k ∧ ExactChromatic G k ∧ AllOddCyclesLong G m

/-- POSITIVE WITNESS: `K₄` has chromatic number four and has no odd cycle of length at most two. -/
theorem GoodBound_witness_pos :
    GoodBound 4 4 2 (⊤ : SimpleGraph (Fin 4)) := by
  decide

/-- NEGATIVE WITNESS: the adjacent bound `m = 3` fails only because `K₄` contains a triangle. -/
theorem GoodBound_witness_neg :
    ¬ GoodBound 4 4 3 (⊤ : SimpleGraph (Fin 4)) := by
  decide

/-- The finite extremal function used here.  The maximum is taken over `m < n`; for
`k > n` the empty family receives the harmless finite default zero, avoiding an
unbounded or empty `sSup`. -/
noncomputable def fK (k n : ℕ) : ℕ :=
  (Finset.range n).sup
    (fun m => if ∃ G : SimpleGraph (Fin n), GoodBound k n m G then m else 0)

/-- A two-sided eventual comparison with the power appearing in the source. -/
def AsympPower (k : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ (1 / (k - 2 : ℝ)) ≤ (fK k n : ℝ) ∧
        (fK k n : ℝ) ≤ C * (n : ℝ) ^ (1 / (k - 2 : ℝ))

/-- The source's question, read literally for every integer `k ≥ 4`. -/
def Question : Prop :=
  ∀ k : ℕ, 4 ≤ k → AsympPower k

/-- The finite witness data are non-vacuous: the `k = 4`, `n = 4`, `m = 2` instance
is realized by the complete graph, while the adjacent bound `m = 3` is not. -/
theorem finite_control :
    GoodBound 4 4 2 (⊤ : SimpleGraph (Fin 4)) ∧
      ¬ GoodBound 4 4 3 (⊤ : SimpleGraph (Fin 4)) := by
  exact ⟨GoodBound_witness_pos, GoodBound_witness_neg⟩

/-- Resolution of Erdős problem #921, recorded by the source as proved by
Kierstead, Szemerédi, and Trotter [KST84].  The derivation is not reproduced here;
the remaining gap is the formal proof of the asymptotic theorem for `fK`. -/
theorem resolution : Question := by
  sorry Erdos921
