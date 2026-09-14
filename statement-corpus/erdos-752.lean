/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $G$ be a graph with minimum degree $k$ and girth $>2s$ (i.e. $G$ contains no cycles of length $\leq 2s$). Must there be $\gg k^s$ many distinct cycle lengths in $G$?
-/

/- 
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#752 : [Er92b] [Er93,p.346] [Er94b] graph theory | cycles A question of Erdős, Faudree, and Schelp, who proved it when $s=2$. The answer is yes, proved by Sudakov and Verstraëte [SuVe08] , who in fact proved that under the assumption of average degree $k$ and girth $>2s$ there are at least $\gg k^s$ many consecutive even integers which are cycle lengths in $G$. Additional thanks to : Raphael Steiner Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #752, https://www.erdosproblems.com/752, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/




import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos752

/-- The degree of a vertex in a finite simple graph, defined as the cardinality
of the subtype of its neighbours. -/
def Degree {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : ℕ :=
  Fintype.card {w : V // G.Adj v w}

/-- A finite graph has minimum degree at least `k`. -/
def MinDegreeAtLeast {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, k ≤ Degree G v

/-- `IsCycleLength G n` means that `G` contains a simple closed walk of
length `n`, encoded by an injective map from `Fin n` whose consecutive
vertices, including the last and first, are adjacent. -/
def IsCycleLength {V : Type} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ hn : 0 < n,
    3 ≤ n ∧
      ∃ f : Fin n → V,
        Function.Injective f ∧
          ∀ i : Fin n,
            G.Adj (f i)
              (f ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)

/-- `ShortCycleFree G s` expresses that `G` has no cycle of length at most
`2s`. This is the formal girth condition used below. -/
def ShortCycleFree {V : Type} (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ 2 * s → ¬ IsCycleLength G n

/-- A finite graph has at least `c * k^s` distinct cycle lengths. The finite
set `L` explicitly witnesses the distinct lengths, avoiding any cardinality
convention for an infinite set of lengths. -/
def HasManyCycleLengths {V : Type} (G : SimpleGraph V) (k s c : ℕ) : Prop :=
  ∃ L : Finset ℕ,
    c * k ^ s ≤ L.card ∧
      ∀ n ∈ L, IsCycleLength G n

/-- The finite-graph version of the source assertion: there is a positive
absolute constant `c` such that every finite graph of minimum degree at least
`k` and girth greater than `2s` has at least `c * k^s` distinct cycle lengths.
This is a finite formalization of the source; the resolution records the
stronger average-degree conclusion and consecutive-even-length conclusion. -/
def FiniteCycleLengthTheorem (k s : ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      MinDegreeAtLeast G k →
        ShortCycleFree G s →
          HasManyCycleLengths G k s c

/-- Sanity control: zero cannot be a cycle length under the definition,
because every cycle length is required to be positive. -/
theorem not_isCycleLength_zero {V : Type} (G : SimpleGraph V) :
    ¬ IsCycleLength G 0 := by
  intro h
  rcases h with ⟨hn, hrest⟩
  omega

/-- Sanity control: every finite graph has minimum degree at least zero. -/
theorem minDegreeAtLeast_zero {V : Type} [Fintype V] (G : SimpleGraph V) :
    MinDegreeAtLeast G 0 := by
  intro v
  exact Nat.zero_le _

/-- The settled result recorded for Erdős problem #752, in the finite
minimum-degree formulation above. The proof is not reproduced here; the
external resolution attributes the stronger result to Sudakov and Verstraëte. -/
theorem finite_cycle_length_theorem (k s : ℕ) :
    FiniteCycleLengthTheorem k s := by
  sorry Erdos752
