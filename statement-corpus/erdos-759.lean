/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
The cochromatic number of $G$, denoted by $\zeta(G)$, is the minimum number of colours needed to colour the vertices of $G$ such that each colour class induces either a complete graph or empty graph. Let $z(S_n)$ be the maximum value of $\zeta(G)$ over all graphs $G$ which can be embedded on $S_n$, the orientable surface of genus $n$. Determine the growth rate of $z(S_n)$.
-/

/-
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#759 : [ErGi93] graph theory | chromatic number A problem of Erdős and Gimbel. Gimbel [Gi86] proved that\[\frac{\sqrt{n}}{\log n}\ll z(S_n) \ll \sqrt{n}.\]Solved by Gimbel and Thomassen [GiTh97] , who proved\[z(S_n) \asymp \frac{\sqrt{n}}{\log n}.\] Additional thanks to : Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave an exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #759, https://www.erdosproblems.com/759, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos759

/-- A coloring of a finite simple graph in which every color class induces either a
complete graph or an empty graph. -/
def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k,
    ∀ i : Fin k,
      (∀ u v : V, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
      (∀ u v : V, c u = i → c v = i → u ≠ v → ¬ G.Adj u v)

/-- The cochromatic number, defined as the least number of colors admitting a
cochromatic coloring. The `sInf` is over a nonempty, bounded set for finite graphs;
the corresponding facts are recorded below so that its default value is not used
silently. -/
noncomputable def cochromatic {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsCochromaticColoring G k}

/-- A basic proved control showing that the coloring predicate has genuine graph
content: the one-vertex empty graph admits a one-color cochromatic coloring. -/
theorem one_vertex_control :
    IsCochromaticColoring (⊥ : SimpleGraph (Fin 1)) 1 := by
  refine ⟨fun _ => 0, ?_⟩
  intro i
  right
  intro u v hu hv huv
  simp

/-- The graphs embeddable on the orientable surface of genus `n`. This predicate
is intentionally left as a named mathematical interface: a full formalization
of embeddings into orientable surfaces remains to be supplied. -/
def OrientablyEmbeddable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  sorry

/-- The set of possible cochromatic numbers of graphs embeddable on the
orientable surface of genus `n`. -/
noncomputable def admissibleValues (n : ℕ) : Set ℕ :=
  {k | ∃ m : ℕ, ∃ G : SimpleGraph (Fin m),
    OrientablyEmbeddable G n ∧ cochromatic G = k}

/-- The quantity `z(S_n)`, represented as the supremum of the cochromatic
numbers of graphs embeddable on the orientable surface of genus `n`. Since
`sSup` returns a default value on empty or unbounded sets, the required
nonemptiness and boundedness controls are stated separately below. -/
noncomputable def surfaceCochromatic (n : ℕ) : ℕ :=
  sSup (admissibleValues n)

/-- Nonemptiness of the set used to define `surfaceCochromatic`; this is needed
to rule out the empty-set default of `sSup`. -/
theorem admissibleValues_nonempty (n : ℕ) :
    (admissibleValues n).Nonempty := by
  sorry

/-- Boundedness of the set used to define `surfaceCochromatic`; this is needed
to rule out the unbounded-set default of `sSup`. -/
theorem admissibleValues_bddAbove (n : ℕ) :
    BddAbove (admissibleValues n) := by
  sorry

/-- The asymptotic statement that the solved resolution records. Here
`surfaceCochromatic n` is `z(S_n)`, and the displayed inequalities express
`z(S_n) \asymp sqrt(n) / log(n)` for all sufficiently large `n`. -/
def SurfaceGrowth : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (Real.sqrt (n : ℝ) / Real.log (n : ℝ)) ≤
          (surfaceCochromatic n : ℝ) ∧
      (surfaceCochromatic n : ℝ) ≤
          C * (Real.sqrt (n : ℝ) / Real.log (n : ℝ))

/-- The formalized resolution of Erdős Problem 759: the maximum cochromatic
number on the orientable surface of genus `n` grows on the order of
`sqrt(n) / log(n)`. The graph-embedding interface above is the remaining
formalization boundary. -/
theorem surfaceCochromatic_growth : SurfaceGrowth := by
  sorry

#print axioms one_vertex_control

end Erdos759
