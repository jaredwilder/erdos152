/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $N\geq 1$. How many integers can be written as the sum of distinct unit fractions with denominators from $\{1,\ldots,N\}$? Are there $o(\log N)$ such integers?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#309 : [ErGr80] number theory | unit fractions If the number of such integers is $N(n)$ then it is trivial that $N(n)\leq \log n+O(1)$. Yokota [Yo97] proved that $N(n)\geq \log n-O(\log\log n)$. Croot [Cr99] proved that every integer at most\[\leq \sum_{n\leq N}\frac{1}{n}-(\tfrac{9}{2}+o(1))\frac{(\log\log N)^2}{\log N}\]can be so represented. If $F(N)$ counts the number of integers which can be represented in this fashion, then the current best lower bound known is\[F(N) \geq \log N+\gamma -\left(\frac{\pi^2}{3}+o(1)\right)\frac{(\log\log N)^2}{\log N}\]due to Yokota [Yo02] . Additional thanks to : Alfaiz, epistemologist, Zach Hunter, and Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 20 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #309, https://www.erdosproblems.com/309, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A217693 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research open








open Classical Filter

namespace Erdos309

/-- The allowed denominators are precisely the positive natural numbers at most `N`. -/
def denominators (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- The finite set of rational sums of distinct unit fractions whose denominators lie in
`{1, ..., N}`.  Distinctness is represented by taking a subset of `denominators N`. -/
def representedValues (N : ℕ) : Finset ℚ :=
  (denominators N).powerset.biUnion
    (fun s => {∑ d ∈ s, (1 : ℚ) / (d : ℚ)})

/-- The integers represented by distinct unit fractions with denominators at most `N`.
The interval `[0,N]` is a finite ambient window: every such sum is nonnegative and is at
most the number of available denominators, hence at most `N`. -/
def representedIntegers (N : ℕ) : Finset ℤ :=
  (Finset.Icc (0 : ℤ) (N : ℤ)).filter
    (fun z => (z : ℚ) ∈ representedValues N)

/-- `F(N)`, the number of integers representable as sums of distinct unit fractions with
denominators from `{1, ..., N}`. -/
def F (N : ℕ) : ℕ :=
  (representedIntegers N).card

/-- The source's asymptotic question, formalized as whether the counting function is
`o(log N)`.  The first clause of the source is answered by the explicitly defined function
`F`; this proposition records its second clause. -/
def Sublogarithmic : Prop :=
  Tendsto (fun N : ℕ => (F N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 0)

/-- The frozen question asks whether `Sublogarithmic` holds; the resolution records strong
lower bounds instead, so this is retained as an open proposition rather than asserted. -/
def Question : Prop :=
  Sublogarithmic

/-- A proved small-case control: for `N = 1`, the only represented integers are `0` and `1`.
This exercises both the distinct-subset encoding and the integer-value filter. -/
theorem representedIntegers_one :
    representedIntegers 1 = ({0, 1} : Finset ℤ) := by
  decide

#print axioms representedIntegers_one

end Erdos309
