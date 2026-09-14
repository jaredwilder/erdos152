/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A\subseteq \mathbb{N}$ be a finite set of size $N$. Is it true that, for any fixed $t$, there are\[\ll \frac{2^N}{N^{3/2}}\]many $S\subseteq A$ such that $\sum_{n\in S}n=t$? If we further ask that $\lvert S\rvert=l$ (for any fixed $l$) then is the number of solutions\[\ll \frac{2^N}{N^2},\]with the implied constant independent of $l$ and $t$?
-/

-- @category research solved

/- 
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#362 : [Er65] [Er73,p.129] [ErGr80,p.59] number theory Erdős and Moser [Er65] proved the first bound with an additional factor of $(\log n)^{3/2}$. This was removed by Sárközy and Szemerédi [SaSz65] , thereby answering the first question in the affirmative. Stanley [St80] has shown that this quantity is maximised when $A=\{-\lfloor \frac{N-1}{2}\rfloor,\ldots,\lfloor\frac{N}{2}\rfloor\}$. The second question was answered in the affirmative by Halász [Ha77] , as a consequence of a more general multi-dimensional result. Additional thanks to : Adrian Beker, Zachary Chase, and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 27 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #362, https://www.erdosproblems.com/362, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical








open Classical Filter

namespace Erdos362

/-- The number of subsets of `A` whose elements sum to `t`. -/
def subsetSumCount (A : Finset ℕ) (t : ℕ) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = t)).card

/-- The number of `l`-element subsets of `A` whose elements sum to `t`. -/
def subsetSumCountCard (A : Finset ℕ) (l t : ℕ) : ℕ :=
  (A.powerset.filter (fun S => S.card = l ∧ S.sum id = t)).card

/-- 
The first affirmative answer, formalized as an eventual uniform upper bound:
for each fixed `t`, the implied constant may depend on `t`, while the exponent
`3/2` is represented by `Real.rpow`. The threshold avoids interpreting the
asymptotic expression at `N = 0`.
-/
def FirstBound : Prop :=
  ∀ t : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A.card = N →
        (subsetSumCount A t : ℝ) ≤
          C * (2 : ℝ) ^ N / Real.rpow (N : ℝ) (3 / 2 : ℝ)

/-- 
The second affirmative answer, formalized as an eventual upper bound whose
constant is independent of both the prescribed cardinality `l` and the target
sum `t`; the source's exponent `2` is represented literally.
-/
def SecondBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N →
      ∀ l t : ℕ, ∀ A : Finset ℕ, A.card = N →
        (subsetSumCountCard A l t : ℝ) ≤
          C * (2 : ℝ) ^ N / (N : ℝ) ^ 2

/-- 
The source records both questions as answered affirmatively by the cited
results of Sárközy--Szemerédi and Halász. The formal derivation of these
nontrivial extremal estimates remains an explicit gap.
-/
theorem resolution_claim : FirstBound ∧ SecondBound := by
  sorry

/-- 
A computed control showing that `subsetSumCount` is neither identically zero
nor identically one: the empty set has exactly one subset summing to zero and
no subset summing to three.
-/
theorem subsetSumCount_control :
    subsetSumCount (∅ : Finset ℕ) 0 = 1 ∧
      subsetSumCount (∅ : Finset ℕ) 3 = 0 := by
  simp [subsetSumCount]

/-- A computed control for the cardinality-refined counting function. -/
theorem subsetSumCountCard_control :
    subsetSumCountCard ({3} : Finset ℕ) 1 3 = 1 ∧
      subsetSumCountCard ({3} : Finset ℕ) 0 3 = 0 := by
  simp [subsetSumCountCard]

#print axioms subsetSumCount_control
#print axioms subsetSumCountCard_control

end Erdos362
