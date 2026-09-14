/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $r_3(N)$ be the size of the largest subset of $\{1,\ldots,N\}$ which does not contain a non-trivial $3$-term arithmetic progression. Prove that $r_3(N)\ll N/(\log N)^C$ for every $C>0$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#140 : [ErGr80,p.11] [Er81] [Er97c] additive combinatorics | arithmetic progressions Proved by Kelley and Meka [KeMe23] . In [ErGr80] and [Er81] it is conjectured that this holds for every $k$-term arithmetic progression. See also [3] . Additional thanks to : Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 20 December 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #140, https://www.erdosproblems.com/140, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A003002 Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace Erdos140

/-- A finite set `S` is free of non-trivial three-term arithmetic progressions
inside the interval `{1, ..., N}`. The bound on the common difference is
harmless because every progression contained in that interval has difference
at most `N`. -/
def IsThreeAPFree (N : ℕ) (S : Finset ℕ) : Prop :=
  ¬ ∃ a ∈ S, ∃ d ∈ Finset.range (N + 1),
    0 < d ∧ a + d ∈ S ∧ a + 2 * d ∈ S

/-- The extremal quantity `r₃(N)`, defined as the largest cardinality of a
three-term-progression-free subset of `{1, ..., N}`. -/
def r3 (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).powerset.filter (IsThreeAPFree N) |>.sup Finset.card

/-- An explicit eventual-bound formulation of the notation
`r₃(N) ≪ N / (log N)^C`, with the implied constant allowed to depend on `C`. -/
def HasPowerSavingBound (C : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ᶠ N : ℕ in Filter.atTop,
      (r3 N : ℝ) ≤ K * ((N : ℝ) / (Real.log (N : ℝ)) ^ C)

/-- The formalized statement of Erdos problem #140. The source says:
“Prove that `r₃(N) ≪ N/(log N)^C` for every `C > 0`.”
Here `HasPowerSavingBound C` is the displayed eventual-bound reading of
that notation, so the statement is `∀ C > 0, HasPowerSavingBound C`.
The resolution node records this statement as proved by Kelley and Meka. -/
def Erdos140Statement : Prop :=
  ∀ C : ℝ, 0 < C → HasPowerSavingBound C

/-- A proved degenerate-instance control: the interval `{1, ..., 0}` is empty,
so its largest progression-free subset has cardinality zero. -/
theorem r3_zero : r3 0 = 0 := by
  classical
  simp [r3, IsThreeAPFree]

#print axioms r3_zero

end Erdos140