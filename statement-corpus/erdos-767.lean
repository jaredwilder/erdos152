/-
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $g_k(n)$ be the maximal number of edges possible on a graph with $n$ vertices which does not contain a cycle with $k$ chords incident to a vertex on the cycle. Is it true that\[g_k(n)=(k+1)n-(k+1)^2\]for $n$ sufficiently large?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#767 : [Er64c] [Er69b] [Er75] graph theory | turan number Czipszer proved that $g_k(n)$ exists for all $k$, and in fact $g_k(n)\leq (k+1)n$. Erdős wrote it is 'easy to see' that\[g_k(n)\geq (k+1)n-(k+1)^2.\]Pósa proved that $g_1(n)=2n-4$ for $n\geq 4$. Erdős could prove the conjectured equality for $n\geq 2k+2$ when $k=2$ or $k=3$. The conjectured equality was proved for $n\geq 3k+3$ by Jiang [Ji04] . Curiously, in [Er69b] Erdős mentions this problem, but states that his conjectured equality for $g_k(n)$ was disproved (for general $k$) by Lewin, citing oral communication. Perhaps Lewin only disproved this for small $n$, or perhaps Lewin's disproof was simply incorrect. Additional thanks to : Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 06 October 2025. ( View history ) ( To view the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #767, https://www.erdosproblems.com/767, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Can be formalisable JoshuaB Working on formalising None Previous Next
-/



import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos767

/-- A cycle on `m` distinct vertices, together with `k` distinct chords
incident to its first vertex.  The three excluded indices are the first
vertex and its two cyclic neighbours. -/
def HasCycleWithKChords (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ m : ℕ, 3 ≤ m ∧
    ∃ p : Fin m → Fin n, Function.Injective p ∧
      (∀ i : Fin m,
        G.Adj (p i) (p ⟨(i.val + 1) % m, Nat.mod_lt _ (by omega)⟩)) ∧
      ∃ q : Fin k → Fin m,
        Function.Injective q ∧
          (∀ j : Fin k,
            q j ≠ 0 ∧ q j ≠ 1 ∧ (q j).val + 1 ≠ m ∧
              G.Adj (p 0) (p (q j)))

/-- A graph is admissible for `g_k(n)` when it contains no cycle with
`k` chords incident to a vertex on that cycle. -/
def Admissible (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ¬ HasCycleWithKChords G k

/-- The number of edges of a finite simple graph. -/
def edgeCount (G : SimpleGraph (Fin n)) : ℕ :=
  G.edgeFinset.card

/-- The set of edge counts of admissible graphs on `n` vertices. -/
def admissibleEdgeCounts (k n : ℕ) : Set ℕ :=
  {e | ∃ G : SimpleGraph (Fin n), Admissible G k ∧ e = edgeCount G}

/-- The extremal function from the source, defined as the supremum of the
finite set of attainable edge counts.  The supremum is used only after
recording below that the set is nonempty and bounded above, so its default
value on empty or unbounded sets is irrelevant. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup (admissibleEdgeCounts k n)

/-- The admissible edge-count set is nonempty: the empty graph is admissible.
This is also an anti-vacuity control for the definition of `g`. -/
theorem admissibleEdgeCounts_nonempty (k n : ℕ) :
    (admissibleEdgeCounts k n).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨⊥, ?_, ?_⟩
  · simp [Admissible, HasCycleWithKChords]
  · simp [edgeCount]

/-- The admissible edge-count set is bounded above by the number of all
possible unordered vertex pairs.  Thus the `sSup` in `g` is not using its
unbounded-set junk value. -/
theorem admissibleEdgeCounts_bddAbove (k n : ℕ) :
    BddAbove (admissibleEdgeCounts k n) := by
  refine ⟨(Finset.univ : Finset (Sym2 (Fin n))).card, ?_⟩
  rintro e ⟨G, hG, rfl⟩
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The edge-count function is nonnegative, and the preceding nonemptiness
and boundedness results justify interpreting `g` as a genuine finite
maximum rather than as a junk supremum. -/
theorem g_nonneg (k n : ℕ) : 0 ≤ g k n := by
  exact Nat.zero_le _

/-- Jiang's settled form of the conjectured equality: the source records that
the equality holds for `n ≥ 3 k + 3`.  The remaining gap is the imported
mathematical theorem of Jiang, not a definitional or order-theoretic step.

The source asks whether the displayed equality holds for sufficiently large
`n`; the resolution answers yes with the explicit threshold `3 k + 3`.
The left side is the extremal number of admissible graphs defined above, and
the right side is exactly `(k+1)n-(k+1)^2`. -/
theorem g_eq_eventually (k n : ℕ) (hn : 3 * k + 3 ≤ n) :
    g k n = (k + 1) * n - (k + 1) ^ 2 := by
  sorry

#print axioms g_eq_eventually

end Erdos767
