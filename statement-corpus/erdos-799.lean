/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
The list chromatic number $\chi_L(G)$ is defined to be the minimal $k$ such that for any assignment of a list of $k$ colours to each vertex of $G$ (perhaps different lists for different vertices) a colouring of each vertex by a colour on its list can be chosen such that adjacent vertices receive distinct colours. Is it true that $\chi_L(G)=o(n)$ for almost all graphs on $n$ vertices?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#799 : [ERT80] graph theory | chromatic number A problem of Erdős, Rubin and Taylor. The answer is yes: Alon [Al92] proved that in fact the random graph on $n$ vertices with edge probability $1/2$ has\[\chi_L(G) \ll \frac{\log\log n}{\log n}n\]almost surely. Alon, Krivelevich, and Sudakov [AKS99] improved this to\[\chi_L(G) \asymp \frac{n}{\log n}\]almost surely. Additional thanks to : David Penman Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #799, https://www.erdosproblems.com/799, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved




open Classical Filter

namespace Erdos799

/-- `ListColorable G k` means that every assignment of `k`-element finite
lists of natural-number colours admits a proper list-colouring of `G`. -/
def ListColorable {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ L : Fin n → Finset ℕ,
    (∀ v, (L v).card = k) →
      ∃ c : Fin n → ℕ,
        (∀ v, c v ∈ L v) ∧
          (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v)

/-- A decidable finite approximation to list-colourability, restricting colours
to `Fin q`; this is the bounded predicate used for concrete computational
controls. -/
def ListColorableFinite {n q : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ L : Fin n → Finset (Fin q),
    (∀ v, (L v).card = k) →
      ∃ c : Fin n → Fin q,
        (∀ v, c v ∈ L v) ∧
          (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v)

/-- The graph on two vertices having its single possible edge. -/
def singleEdge : SimpleGraph (Fin 2) where
  Adj u v := u ≠ v
  symm := by
    intro u v huv
    exact Ne.symm huv
  loopless := by
    intro u
    exact ne_of_eq rfl

/-- POSITIVE WITNESS: one vertex with singleton lists is list-colourable. -/
theorem listColorable_witness_pos :
    ListColorable (⊥ : SimpleGraph (Fin 1)) 1 := by
  intro L hL
  let c : Fin 1 → ℕ := fun v => (L v).choose
  have hc : ∀ v, c v ∈ L v := by
    intro v
    exact (L v).choose_spec (by
      have hcard : (L v).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have : (L v).card = 0 := by simp [hempty]
        omega
      exact hcard)
  exact ⟨c, hc, by simp⟩

/-- NEGATIVE WITNESS: adding the single edge to the positive one and assigning
the same singleton list to both vertices destroys list-colourability. -/
theorem listColorable_witness_neg :
    ¬ ListColorable singleEdge 1 := by
  intro h
  let L : Fin 2 → Finset ℕ := fun _ => {0}
  obtain ⟨c, hc, hproper⟩ := h L (by intro v; simp)
  have h0 : c (0 : Fin 2) = 0 := by
    have := hc (0 : Fin 2)
    simpa using this
  have h1 : c (1 : Fin 2) = 0 := by
    have := hc (1 : Fin 2)
    simpa using this
  have hedge : singleEdge.Adj (0 : Fin 2) (1 : Fin 2) := by
    simp [singleEdge]
  exact (hproper hedge) (h0.trans h1.symm)

/-- POSITIVE BOUNDED WITNESS: the empty two-vertex graph is colourable from
every singleton list over `Fin 2`. -/
theorem listColorableFinite_witness_pos :
    ListColorableFinite (⊥ : SimpleGraph (Fin 2)) 1 := by
  decide

/-- NEGATIVE BOUNDED WITNESS: the near-miss obtained by adding the sole edge
fails for the constant singleton list assignment. -/
theorem listColorableFinite_witness_neg :
    ¬ ListColorableFinite (q := 2) singleEdge 1 := by
  decide

/-- The list chromatic number, defined as the infimum of the admissible list
sizes.  This is a noncomputable definition because `sInf` supplies the minimum
of a set of natural numbers. -/
noncomputable def listChromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ListColorable G k}

/-- The admissible list-size set is nonempty for every finite graph: lists of
size equal to the number of vertices admit a proper list-colouring.  The proof
is left as the mathematical input needed to justify the `sInf` definition. -/
theorem listColorable_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set.Nonempty {k : ℕ | ListColorable G k} := by
  sorry

/-- The admissible list-size set is bounded above by the number of vertices.
This control prevents the `sInf`-based definition from relying on junk values. -/
theorem listColorable_bddAbove {n : ℕ} (G : SimpleGraph (Fin n)) :
    BddAbove {k : ℕ | ListColorable G k} := by
  sorry

/-- The finite probabilistic formulation of the source question: for every
positive real `ε`, eventually the proportion of graphs on `n` labelled
vertices whose list chromatic number is at most `ε n` exceeds `1 - ε`.
The source says “almost all graphs”; here “almost all” is represented by this
uniform counting statement over the finite type of labelled simple graphs. -/
def AlmostAllListChromaticSublinear : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ((Finset.univ.filter
          (fun G : SimpleGraph (Fin n) =>
            (listChromaticNumber G : ℝ) ≤ ε * n)).card : ℝ) /
          (Fintype.card (SimpleGraph (Fin n)) : ℝ) >
        1 - ε

/-- Alon's resolution of Erdős Problem #799.  The frozen resolution records
that the answer is yes; the probabilistic asymptotic theorem itself is retained
here as an explicit literature-dependent proof gap rather than as an axiom. -/
theorem alon_resolution : AlmostAllListChromaticSublinear := by
  sorry Erdos799
