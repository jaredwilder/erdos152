/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $N\geq 1$. What is the size of the largest $A\subset \{1,\ldots,N\}$ such that $[a,b]\leq N$ for all $a,b\in A$, where $[a,b]$ is the least common multiple of $a$ and $b$? Is it attained by choosing all integers in $[1,(N/2)^{1/2}]$ together with all even integers in $[(N/2)^{1/2},(2N)^{1/2}]$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#441 : [Er51b] [Er65,p.183] [Er73,p.134] [ErGr80,p.87] [Er98] number theory Let $g(N)$ denote the size of the largest such $A$. The construction mentioned proves that\[g(N) \geq \left(\tfrac{9}{8}n\right)^{1/2}+O(1).\]Erdős [Er51b] proved $g(N) \leq (4n)^{1/2}+O(1)$, which was improved by Choi [Ch72b] . Chen [Ch98] established the asymptotic\[g(N) \sim \left(\tfrac{9}{8}n\right)^{1/2}.\]Chen and Dai [DaCh06] proved that\[g(N)\leq \left(\tfrac{9}{8}n\right)^{1/2}+O\left(\left(\frac{N}{\log N}\right)^{1/2}\log\log N\right).\]In [ChDa07] the same authors prove that, infinitely often, Erdős' construction is not optimal: if $B$ is that construction and $A$ is such that $\lvert A\rvert=g(N)$ then, for infinitely many $N$,\[\lvert A\rvert\geq \lvert B\rvert+t,\]where $t\geq 0$ is defined such that the $t$-fold iterated logarithm of $N$ is in $[0,1)$. This is discussed in problems B26 and E2 of Guy's collection [Gu04] . Additional thanks to : Terence Tao and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 27 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #441, https://www.erdosproblems.com/441, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A068509 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





-- @category research solved

import Mathlib
open Classical
open Filter







open Classical Filter

namespace Erdos441

/-- A finite set of positive integers is admissible at `N` when every pair has
least common multiple at most `N`. -/
def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N

/-- The set of cardinalities of admissible finite sets at `N`. -/
def SizeSet (N : ℕ) : Set ℕ :=
  {k | ∃ A : Finset ℕ, Admissible N A ∧ A.card = k}

/-- The size of the largest admissible set, represented as the supremum of all
admissible cardinalities. The `sSup` junk-value issue is controlled below by
proved nonemptiness and boundedness of `SizeSet N`. -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup (SizeSet N)

/-- The integer-rounding interpretation of Erdős' proposed construction:
integers from `1` through `√(N/2)`, together with even integers from
`√(N/2)` through `√(2N)`. -/
def construction (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 (Nat.sqrt (N / 2)) ∪
    (Finset.Icc (Nat.sqrt (N / 2)) (Nat.sqrt (2 * N))).filter
      (fun k => k % 2 = 0)

/-- A finite admissible set is largest when every other admissible set has no
greater cardinality. -/
def IsLargest (N : ℕ) (A : Finset ℕ) : Prop :=
  Admissible N A ∧ ∀ B : Finset ℕ, Admissible N B → B.card ≤ A.card

/-- The original question, formalized with natural-number square-root
rounding in the displayed construction. -/
def OriginalQuestion : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    (∃ A : Finset ℕ, IsLargest N A) ∧ IsLargest N (construction N)

/-- The source's asymptotic resolution, expressed as convergence after scaling
by `√N`. This declaration records the literature result and remains an
explicit proof gap: no proof of Chen's asymptotic is supplied here. -/
def ChenAsymptotic : Prop :=
  Tendsto (fun N : ℕ => (g N : ℝ) / Real.sqrt (N : ℝ))
    atTop (𝓝 (Real.sqrt ((9 : ℝ) / 8)))

/-- The source's statement that the proposed construction is not optimal
infinitely often, expressed using the integer-rounded construction above.
This is a named formal claim whose proof remains to be supplied. -/
def ConstructionNotAlwaysOptimal : Prop :=
  ∃ᶠ N : ℕ in atTop,
    ∃ A : Finset ℕ, Admissible N A ∧
      (construction N).card < A.card

/-- The admissible cardinality set is nonempty because the empty set is
admissible. This also prevents the lower-bound direction of `sSup` from
resting on the default value of an empty supremum. -/
theorem sizeSet_nonempty (N : ℕ) : (SizeSet N).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨∅, ?_, by simp⟩
  simp [Admissible]

/-- Every admissible cardinality at `N` is at most `N + 1`; hence the
supremum defining `g N` is bounded above. Together with `sizeSet_nonempty`,
this controls both empty-set and unbounded-set junk in `sSup`. -/
theorem sizeSet_bddAbove (N : ℕ) : BddAbove (SizeSet N) := by
  refine ⟨N + 1, ?_⟩
  rintro k ⟨A, hA, rfl⟩
  have hsub : A ⊆ Finset.range (N + 1) := by
    intro a ha
    have haN : a ≤ N := (hA.1 a ha).2
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le haN
  have hcard := Finset.card_le_card hsub
  simpa using hcard

/-- A concrete control exercising the least-common-multiple predicate:
the singleton `{1}` is admissible at `N = 1`, so cardinality one belongs to
`SizeSet 1`. -/
theorem one_mem_sizeSet_one : 1 ∈ SizeSet 1 := by
  refine ⟨{1}, ?_, by simp⟩
  simp [Admissible]

/-- The asymptotic result recorded in the resolution node. The derivation is
not proved in this artifact; the remaining gap is the deep number-theoretic
theorem of Chen. -/
theorem chen_asymptotic : ChenAsymptotic := by
  sorry

/-- The resolution's infinitely-often improvement over Erdős' construction.
The statement is meaningful because `Admissible` refers directly to finite
sets of positive natural numbers and `Nat.lcm`, rather than to a tag or an
opaque label. Its proof remains open in this formalization. -/
theorem construction_not_always_optimal : ConstructionNotAlwaysOptimal := by
  sorry Erdos441

#print axioms Erdos441.sizeSet_nonempty
#print axioms Erdos441.sizeSet_bddAbove
#print axioms Erdos441.one_mem_sizeSet_one
