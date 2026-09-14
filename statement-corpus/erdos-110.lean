/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is there some $F(n)$ such that every graph with chromatic number $\aleph_1$ has, for all large $n$, a subgraph with chromatic number $n$ on at most $F(n)$ vertices?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#110 : [EHS82] [Er87] [Er90] [Er95d] [Er97f] graph theory | chromatic number | cycles Conjectured by Erdős, Hajnal, and Szemerédi [EHS82] . This fails if the graph has chromatic number $\aleph_0$. A theorem of de Bruijn and Erdős [dBEr51] implies that, if $G$ has infinite chromatic number, then $G$ has a finite subgraph of chromatic number $n$ for every $n\geq 1$. In [Er95d] Erdős suggests this is true, although such an $F$ must grow faster than the $k$-fold iterated exponential function for any $k$. Shelah [KoSh05] proved that it is consistent that the answer is no. Lambie-Hanson [La20] constructed a counterexample in ZFC. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (5) Proof claims (0) More information and links This page was last edited 01 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #110, https://www.erdosproblems.com/110, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/



-- @category research solved







import Mathlib
open Classical Filter

namespace Erdos110

/-- A proper coloring of a simple graph by colors in `C`. -/
def ProperColoring {V : Type} (G : SimpleGraph V) {C : Type}
    (c : V → C) : Prop :=
  ∀ ⦃v w : V⦄, G.Adj v w → c v ≠ c w

/-- `Colorable G k` means that `G` has a proper coloring with `k` colors. -/
def Colorable {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ProperColoring G c

/-- The exact finite chromatic-number condition used for a subgraph. -/
def ExactChromatic {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Colorable G k ∧ ¬ Colorable G (k - 1)

/-- This formalization records the relevant infinite-chromatic lower-bound condition
`¬ ColorableNat G`.  It is weaker than the literal assertion that the chromatic
number is exactly `\aleph_1`; the distinction is left explicit rather than hidden
behind a label. -/
def AlephOneChromatic {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ c : V → ℕ, ProperColoring G c

/-- A finite subgraph witness has finite vertex set, bounded size, and exact chromatic
number `n`.  The `Subgraph` relation is the genuine `SimpleGraph.Subgraph` relation. -/
def BoundedChromaticSubgraph {V : Type} (G : SimpleGraph V) (n b : ℕ) : Prop :=
  ∃ H : G.Subgraph,
    H.verts.Finite ∧ Nat.card H.verts ≤ b ∧
      ExactChromatic (H.coe : SimpleGraph H.verts) n

/-- The question, formalized with the explicit infinite-chromatic lower-bound reading
of `\aleph_1` described in `AlephOneChromatic`: does one function bound finite
subgraphs of every sufficiently large exact chromatic number? -/
def Question : Prop :=
  ∃ F : ℕ → ℕ,
    ∀ (V : Type) (G : SimpleGraph V),
      AlephOneChromatic G →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          BoundedChromaticSubgraph G n (F n)

/-- A one-vertex edgeless graph has exact chromatic number one.  This is a proved
control showing that `ExactChromatic` is not merely a vacuous tag predicate. -/
theorem singleton_exact_chromatic :
    ExactChromatic (⊥ : SimpleGraph (Fin 1)) 1 := by
  constructor
  · refine ⟨fun _ => 0, ?_⟩
    intro v w h
    simp at h
  · intro h
    rcases h with ⟨c, _⟩
    exact Fin.elim0 (c 0)

/-- A one-vertex graph is not `AlephOneChromatic`, since its constant natural-valued
coloring is proper.  This is a proved control for the infinite-chromatic predicate. -/
theorem singleton_not_alephOneChromatic :
    ¬ AlephOneChromatic (⊥ : SimpleGraph (Fin 1)) := by
  intro h
  apply h
  refine ⟨fun _ => 0, ?_⟩
  intro v w hv
  simp at hv

/-- The source records that the proposed universal bound is false in ZFC, by the
counterexample attributed to Lambie-Hanson [La20].  The mathematical counterexample
and its translation to the explicit `SimpleGraph` formulation remain to be formalized. -/
theorem resolution : ¬ Question := by
  sorry Erdos110
