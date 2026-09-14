/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
How large can $A\subseteq \{1,\ldots,N\}$ be if $A+A$ contains no square numbers?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#438 : [Er80,p.105] [Er80c] [ErGr80,p.87] [Er82e,p.68] number theory Taking all integers $\equiv 1\pmod{3}$ shows that $\lvert A\rvert\geq N/3$ is possible. This can be improved to $\tfrac{11}{32}N$ by taking all integers $\equiv 1,5,9,13,14,17,21,25,26,29,30\pmod{32}$, as observed by Massias. Lagarias, Odlyzko, and Shearer [LOS83] proved this is sharp for the modular version of the problem; that is, if $A\subseteq \mathbb{Z}/N\mathbb{Z}$ is such that $A+A$ contains no squares then $\lvert A\rvert\leq \tfrac{11}{32}N$. They also prove the general upper bound of $\lvert A\rvert\leq 0.475N$ for the integer problem. In fact $\frac{11}{32}$ is sharp in general, as shown by Khalfalah, Lodha, and Szemerédi [KLS02] , who proved that the maximal such $A$ satisfies $\lvert A\rvert\leq (\tfrac{11}{32}+o(1))N$. See also [439] and [587] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 07 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #438, https://www.erdosproblems.com/438, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A363069 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


-- @category research solved

import Mathlib
open Classical
open Filter








open Classical Filter

namespace Erdos438

/-- A natural number is a square if it is the product of a natural number with itself. -/
def IsSquareNat (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k * k

/-- A finite set is admissible when every pairwise sum of its elements is not a square. -/
def SquareAvoiding (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquareNat (a + b)

/-- `Good N A` formalizes `A ⊆ {1, ..., N}` and the condition that `A + A`
contains no square numbers. -/
def Good (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ SquareAvoiding A

/-- The largest cardinality among square-avoiding subsets of `{1, ..., N}`.
The finite supremum is over an explicitly finite family, so no unbounded or
empty `sSup`/`sInf` default is involved. -/
noncomputable def maxGoodCard (N : ℕ) : ℕ :=
  ((Finset.powerset (Finset.Icc 1 N)).filter (Good N)).sup Finset.card

/-- The number `2` is not a natural square. -/
theorem not_square_two : ¬ IsSquareNat 2 := by
  rintro ⟨k, hk⟩
  have hkbound : k ≤ 2 := by
    nlinarith
  interval_cases k <;> norm_num at hk

/-- A concrete anti-vacuity control: for every `N ≥ 1`, the singleton `{1}`
is a valid square-avoiding subset of `{1, ..., N}`. -/
theorem control_singleton_one_good {N : ℕ} (hN : 1 ≤ N) :
    Good N ({1} : Finset ℕ) := by
  constructor
  · intro x hx
    have hx' : x = 1 := by
      simpa using hx
    subst x
    simp [Finset.mem_Icc, hN]
  · intro a ha b hb hs
    have ha' : a = 1 := by
      simpa using ha
    have hb' : b = 1 := by
      simpa using hb
    subst a
    subst b
    apply not_square_two
    simpa using hs

/-- The settled resolution of Erdős Problem 438: the maximal cardinality
has asymptotic density `11/32`. The source records this as sharp in general;
the analytic-number-theoretic proof is not reproduced here and remains an
explicit honest proof gap. -/
theorem maxGoodCard_tendsto :
    Tendsto (fun N : ℕ => (maxGoodCard N : ℝ) / (N : ℝ))
      atTop (𝓝 ((11 : ℝ) / 32)) := by
  sorry

#print axioms not_square_two
#print axioms control_singleton_one_good

end Erdos438
