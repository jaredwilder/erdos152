/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $1=d_1<\cdots <d_{\tau(n)}=n$ be the divisors of $n$ and\[G(n) = \sum_{1\leq i<\tau(n)}\frac{d_i}{d_{i+1}}.\]Is it true that $G(n)\to \infty$ for almost all $n$? Can one prove an asymptotic formula for $\sum_{n\leq X}G(n)$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#673 : [Er79e] [Er82e] number theory | divisors Erdős writes it is 'easy' to prove $\frac{1}{X}\sum_{n\leq X}G(n)\to \infty$. Terence Tao has observed that, for any divisor $m\mid n$,\[\frac{\tau(n/m)}{m} \leq G(n) \leq \tau(n),\]and hence for example $\tau(n)/4\leq G(n)\leq \tau(n)$ for even $n$. It is easy to then see that $G(n)$ grows on average, and in general behaves very similarly to $\tau(n)$ (and in particular the answer to the first question is yes). Tao suggests that this was a mistaken conjecture of Erdős, which he soon corrected a year later to [448] . Indeed, in [Er82e] Erdős recalls this conjecture and observes that it is indeed trivial that $G(n)\to \infty$ for almost all $n$, and notes that he and Tenenbaum proved that $G(n)/\tau(n)$ has a continuous distribution function. Additional thanks to : Terence Tao Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #673, https://www.erdosproblems.com/673, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/





import Mathlib
open Classical
open Filter
open scoped BigOperators Topology

-- @category research open







open Classical Filter

namespace Erdos673

/-- The number of positive divisors of `n`, denoted by `τ(n)` in the source. -/
def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/-- The increasing list of divisors used to interpret the source's
notation `1 = d₁ < ⋯ < d_{τ(n)} = n`. -/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- The divisor-ratio sum
`G(n) = ∑_{1 ≤ i < τ(n)} d_i / d_{i+1}`.
The list lookup is total in Lean; on the mathematically relevant positive
values of `n`, all indices in the displayed range are valid. -/
noncomputable def G (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((divisorList n).length - 1),
    ((divisorList n).get! i : ℝ) /
      ((divisorList n).get! (i + 1) : ℝ)

/-- The proportion, among integers at most `X`, for which `G(n)` does not
exceed the threshold `C`. The denominator is `X`; the value at `X = 0` is
Lean's ordinary division convention and is irrelevant to the limit at infinity. -/
noncomputable def sublevelProportion (C : ℝ) (X : ℕ) : ℝ :=
  ((Finset.filter (fun n => G n ≤ C) (Finset.range (X + 1))).card : ℝ) /
    (X : ℝ)

/-- A precise natural-density formulation of “`G(n) → ∞` for almost all `n`”. -/
def AlmostAllGrowth : Prop :=
  ∀ C : ℝ, Tendsto (sublevelProportion C) atTop (𝓝 0)

/-- The normalized average of `G(n)` over `n ≤ X`. -/
noncomputable def average (X : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (X + 1), G n) / (X : ℝ)

/-- The average-growth assertion recorded as easy in the resolution. -/
def AverageDiverges : Prop :=
  Tendsto average atTop atTop

/-- The first question from the source together with the average-divergence
statement explicitly recorded in its resolution. The stronger request for a
specific asymptotic formula is not encoded here, since the frozen resolution
does not provide such a formula. -/
def Question : Prop :=
  AlmostAllGrowth ∧ AverageDiverges

/-- Proved control: the divisor-count definition has the expected value
`τ(1) = 1`, so it is not an empty placeholder for the divisor function. -/
theorem tau_one : tau 1 = 1 := by
  simp [tau]

#print axioms tau_one

/-- The resolution states that `G(n)` tends to infinity for almost all `n`
and that its normalized average tends to infinity. A formal proof of these
number-theoretic facts remains to be supplied; the frozen source also leaves
the requested asymptotic formula unspecified. -/
theorem resolution_claim : Question := by
  sorry Erdos673
