/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $A$ be a finite set of integers. Is it true that, for every $k$, if $\lvert A\rvert$ is sufficiently large depending on $k$, then there are least $\lvert A\rvert^k$ many integers which are either the sum or product of distinct elements of $A$?
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#53 : [Er77c] [ErGr80] [ErSz83] [Er91] [Er97] [Er97e] number theory | additive combinatorics Asked by Erdős and Szemerédi [ErSz83] . Solved in this form by Chang [Ch03] . Erdős and Szemerédi proved that there exist arbitrarily large sets $A$ such that the number of integers which are the sum or product of distinct elements of $A$ is at most\[\exp\left(c (\log \lvert A\rvert)^2\log\log\lvert A\rvert\right)\]for some constant $c>0$. See also [52] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #53, https://www.erdosproblems.com/53, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/

import Mathlib

-- @category research solved

namespace ErdosProblem53

/-- The nonempty subsets of a finite set `A` of integers. -/
def nonemptySubsets (A : Finset ℤ) : Finset (Finset ℤ) :=
  A.powerset.filter (fun s : Finset ℤ => s.Nonempty)

/-- The integers obtained as sums of distinct elements of `A`, using nonempty subsets. -/
def sumValues (A : Finset ℤ) : Finset ℤ :=
  (nonemptySubsets A).image (fun s => s.sum id)

/-- The integers obtained as products of distinct elements of `A`, using nonempty subsets. -/
def productValues (A : Finset ℤ) : Finset ℤ :=
  (nonemptySubsets A).image (fun s => s.prod id)

/-- The integers which are either a sum or a product of distinct elements of `A`. -/
def sumProductValues (A : Finset ℤ) : Finset ℤ :=
  sumValues A ∪ productValues A

/-- 
The question from the source, read as saying “at least `|A|^k` many”.
The source says “least”; this formalization uses the standard intended
inequality `at least`.  The phrase “sufficiently large depending on `k`”
is represented by a threshold `N` depending on `k`.
-/
def Question : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
    A.card ^ k ≤ (sumProductValues A).card

/-- 
The quantitative upper-bound statement recorded in the resolution: there is
a fixed positive constant `c` and arbitrarily large finite sets for which the
number of distinct sums and products is bounded by
`exp (c (log |A|)^2 log log |A|)`.
-/
def RecordedUpperBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ M : ℕ, ∃ A : Finset ℤ,
      M ≤ A.card ∧
        ((sumProductValues A).card : ℝ) ≤
          Real.exp
            (c * (Real.log (A.card : ℝ)) ^ 2 *
              Real.log (Real.log (A.card : ℝ)))

/-- 
The source records `Question` as solved by Chang.  This declaration records
that resolved status without introducing an unproved theorem into the kernel.
-/
def ChangResolution : Prop :=
  Question

/-- A computed sanity check: the singleton set has exactly one nonempty sum-or-product value. -/
theorem singleton_control :
    (sumProductValues ({0} : Finset ℤ)).card = 1 := by
  simp [sumProductValues, sumValues, productValues, nonemptySubsets]

#print axioms singleton_control

end ErdosProblem53