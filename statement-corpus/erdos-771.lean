
/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)$ be maximal such that, for every $m\geq 1$, there exists some $S\subseteq \{1,\ldots,n\}$ with $\lvert S\rvert=f(n)$ such that $m\neq \sum_{a\in A}a$ for all $A\subseteq S$. Is it true that\[f(n) = \left(\frac{1}{2}+o(1)\right)\frac{n}{\log n}?\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#771 : [Er89] number theory A conjecture of Erdős and Graham, who proved the lower bound\[f(n)\geq \left(\frac{1}{2}+o(1)\right)\frac{n}{\log n}.\]Their proof is to note that we can assume that $m< \binom{n+1}{2}$ and then, for any $m$, take $S=\{ kp : 1\leq k<\frac{n}{p}\}$ where $p$ is the least prime that does not divide $m$ (so $p<(2+o(1))\log n$). The complementary bound\[f(n) \leq \left(\frac{1}{2}+o(1)\right)\frac{n}{\log n}\]was proved by Alon and Freiman [AlFr88] , who chose $m$ as the least common multiple of $\{1,\ldots,s\}$ where $s$ is maximal such that $m\leq \frac{n^2}{20(\log n)^2}$. Additional thanks to : Noga Alon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #771, https://www.erdosproblems.com/771, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/

-- @category research solved

import Mathlib
open Classical
open Filter Topology








open Classical Filter

namespace Erdos771

/-- `Avoids m S` means that no subset sum of `S` is equal to the positive integer `m`. -/
def Avoids (m : ℕ) (S : Finset ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ S → m ≠ ∑ a ∈ A, a

/-- A set of cardinality `k` is admissible for `n` when it works for every positive `m`,
as in the source definition of `f(n)`. -/
def Admissible (n k : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 n ∧ S.card = k ∧ Avoids m S

/-- The extremal cardinality from the source, represented as the supremum of the
set of admissible cardinalities.  The supremum is used only after recording that
the defining set is nonempty and bounded above, so its default-value behavior is
not being relied upon. -/
noncomputable def extremalSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | Admissible n k}

/-- The empty set is admissible for every `n`, since all relevant integers are positive. -/
theorem admissible_zero (n : ℕ) : Admissible n 0 := by
  intro m hm
  refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro A hA
  have hAe : A = ∅ := Finset.subset_empty.mp hA
  subst A
  have hm0 : m ≠ 0 := by omega
  simpa [hm0]

/-- Every admissible cardinality is at most `n`, because the underlying set is
contained in the interval `{1, ..., n}`. -/
theorem admissible_le (n k : ℕ) (hk : Admissible n k) : k ≤ n := by
  obtain ⟨S, hS, hcard, _⟩ := hk 1 (by omega)
  have hcardle : S.card ≤ (Finset.Icc 1 n).card :=
    Finset.card_le_card hS
  have hIcc : (Finset.Icc 1 n).card = n := by
    simp
    omega
  rw [hcard, hIcc] at hcardle
  exact hcardle

/-- The set of admissible cardinalities is nonempty.  This is recorded explicitly
to rule out the empty-set junk value of `sSup`. -/
theorem admissible_nonempty (n : ℕ) :
    ({k : ℕ | Admissible n k} : Set ℕ).Nonempty := by
  exact ⟨0, admissible_zero n⟩

/-- The set of admissible cardinalities is bounded above.  This is recorded
explicitly to rule out the unbounded-set junk value of `sSup`. -/
theorem admissible_bddAbove (n : ℕ) :
    BddAbove ({k : ℕ | Admissible n k} : Set ℕ) := by
  refine ⟨n, ?_⟩
  intro k hk
  exact admissible_le n k hk

/-- Sanity control: the empty set is admissible when `n = 1`, while a singleton
cannot be admissible, since it must be `{1}` and then represents `m = 1`. -/
theorem small_case_control :
    Admissible 1 0 ∧ ¬ Admissible 1 1 := by
  constructor
  · exact admissible_zero 1
  · intro h
    obtain ⟨S, hsub, hcard, havoid⟩ := h 1 (by omega)
    have hpos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hxI : x ∈ Finset.Icc 1 1 := hsub hx
    have hx1 : x = 1 := by
      simp only [Finset.mem_Icc] at hxI
      omega
    have hS : S = {1} := by
      ext y
      constructor
      · intro hy
        have hyI : y ∈ Finset.Icc 1 1 := hsub hy
        have hy1 : y = 1 := by
          simp only [Finset.mem_Icc] at hyI
          omega
        simpa [hy1]
      · intro hy
        have hy1 : y = 1 := by simpa using hy
        subst y
        simpa [hx1] using hx
    have hbad := havoid S (by exact Finset.Subset.rfl)
    rw [hS] at hbad
    simpa using hbad

/-- The asymptotic equality asked for in the source, expressed as convergence of
the normalized extremal cardinality to `1/2`. -/
def AsymptoticFormula : Prop :=
  Tendsto
    (fun n : ℕ =>
      (extremalSize n : ℝ) / ((n : ℝ) / Real.log n))
    atTop (𝓝 (1 / 2 : ℝ))

/-- Resolution of Erdős problem 771.  The source records the lower bound of
Erdős--Graham and the complementary upper bound of Alon--Freiman, which together
give the displayed asymptotic formula.  The formal proof of those deep bounds
is not included here; this theorem is therefore an honest formalization gap. -/
theorem resolution : AsymptoticFormula := by
  sorry Erdos771񟟙
