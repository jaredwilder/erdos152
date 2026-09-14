/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
If $G$ is a graph with infinite chromatic number and $a_1<a_2<\cdots $ are lengths of the odd cycles of $G$ then $\sum \frac{1}{a_i}=\infty$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#57 : [ErHa66] [Er69b] [Er74d] [Er81] [Er90] [Er93,p.342] [Er94b] [Er95] [Er95d] [Er96] [Er97b] [Va99,3.58] graph theory | chromatic number | cycles Conjectured by Erdős and Hajnal [ErHa66] , and solved by Liu and Montgomery [LiMo20] . In [Er81] Erdős asks whether the $a_i$ must in fact have positive upper density, and in [Er95d] and [Er96] he speculates whether the upper density (or even upper logarithmic density) must be $\geq 1/2$. The lower density of the set can be $0$ since there are graphs of arbitrarily large chromatic number and girth. See also [65] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #57, https://www.erdosproblems.com/57, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




-- @category research solved

import Mathlib
namespace ErdosProblem57

/-- The successor of a vertex index on a cyclically ordered set of size `n`. -/
def cycleNext (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- `OddCycleLength G n` means that `G` contains an injectively parametrized odd
cycle of length `n`. -/
def OddCycleLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  3 ≤ n ∧ Nat.Odd n ∧
    ∃ hn : 0 < n,
      ∃ f : Fin n → V,
        Function.Injective f ∧
          ∀ i : Fin n, G.Adj (f i) (f (cycleNext n hn i))

/-- A proper coloring of a graph by `k` colors. -/
def ProperColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

/-- `InfiniteChromatic G` means that `G` has no proper coloring by any finite
number of colors. -/
def InfiniteChromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ¬ ∃ c : V → Fin k, ProperColoring G k c

/-- The partial sum of the reciprocals of the entries of an increasing sequence. -/
def PartialReciprocalSum (a : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (a i : ℝ)⁻¹

/-- The reciprocal series of `a` diverges when its partial sums are unbounded above. -/
def ReciprocalSeriesDiverges (a : ℕ → ℕ) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, R < PartialReciprocalSum a N

/-- A one-vertex edgeless graph is not infinitely chromatic. This is a proved
control exercising the definition of infinite chromatic number. -/
theorem finite_chromatic_control :
    ¬ InfiniteChromatic (⊥ : SimpleGraph PUnit) := by
  intro h
  obtain ⟨c, hc⟩ := h 1
  have hne : c PUnit.unit ≠ c PUnit.unit :=
    hc (v := PUnit.unit) (w := PUnit.unit) (by simp)
  exact hne rfl

/-- The edgeless graph has no odd cycle of length three. This is a proved
control exercising the definition of odd cycle length. -/
theorem odd_cycle_control :
    ¬ OddCycleLength (⊥ : SimpleGraph PUnit) 3 := by
  intro h
  rcases h with ⟨_, _, ⟨hn, f, _, hf⟩⟩
  have he := hf ⟨0, by omega⟩
  simp at he

/-- The formalized content of Erdős Problem #57.

SOURCE mapping: the source says that `G` has infinite chromatic number and that
`a₁ < a₂ < ⋯` are the lengths of the odd cycles of `G`, with divergent
reciprocal sum. Here `a : ℕ → ℕ` is indexed from zero, `StrictMono a`
expresses the displayed increasing sequence, and `OddCycleLength G n ↔
∃ i, a i = n` says that the sequence enumerates exactly the odd cycle lengths.
The resolution node records this assertion as solved by Liu and Montgomery. -/
theorem erdos_57 :
    ∀ {V : Type*} (G : SimpleGraph V),
      InfiniteChromatic G →
        ∀ (a : ℕ → ℕ),
          StrictMono a →
            (∀ n : ℕ, OddCycleLength G n ↔ ∃ i : ℕ, a i = n) →
              ReciprocalSeriesDiverges a := by
  intro V G hchrom a hain hlengths
  sorry

end ErdosProblem57
