/-
SOURCE (frozen), node `n000-question`, VERBATIM:
The density of integers which have two divisors $d_1,d_2$ such that $d_1<d_2<2d_1$ exists and is equal to $1$.

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#144 : [Er61] [Er77c] [Er79] [Er79e] [Er80,p.113] [ErGr80] [Er81h,p.172] [Er82e] [Er85e] [Er97c] [Er98] number theory | divisors In [Er79] asks the stronger version with $2$ replaced by any constant $c>1$. The answer is yes (also to this stronger version), proved by Maier and Tenenbaum [MaTe84] . (Tenenbaum has told me that they received \$650 for their solution.) In [Er64h] claimed a proof that the set of integers $n$ with divisors\[d_1<d_2<d_1(1+(\log n)^{-\beta})\]has density $1$ if $\beta<\log 3-1$, but this claim was retracted in [ErHa79] . Erdős and Hall [ErHa79] proved that this set has density $0$ if $\beta >\log 3-1$ (in a stronger quantitative form). The proof of Maier and Tenenbaum [MaTe84] proves that the density is $1$ if $\beta<\log 3-1$. This is discussed in problem E3 of Guy's collection [Gu04] . See also [449] and [884] . Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 08 April 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #144, https://www.erdosproblems.com/144, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A005279 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None
-/

import Mathlib

-- @category research solved

namespace Erdos144

/-- The integers having two divisors in the multiplicative interval `(d₁, c d₁)`. -/
def HasCloseDivisors (c : ℝ) (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ,
    d₁ ∣ n ∧ d₂ ∣ n ∧
      (d₁ : ℝ) < d₂ ∧ (d₂ : ℝ) < c * d₁

/-- The set of integers having two divisors with ratio strictly less than `c`. -/
def closeDivisorSet (c : ℝ) : Set ℕ :=
  {n | HasCloseDivisors c n}

/-- The counting sequence used for natural density, normalized by the size of
the initial segment `0, ..., N - 1`. -/
noncomputable def densitySequence (s : Set ℕ) (N : ℕ) : ℝ := by
  classical
  exact
    (((Finset.range N).filter (fun n => n ∈ s)).card : ℝ) / (N : ℝ)

/-- The assertion that a set of integers has natural density one. -/
def HasNaturalDensityOne (s : Set ℕ) : Prop :=
  Tendsto (densitySequence s) Filter.atTop (𝓝 (1 : ℝ))

/-- The stronger density-one assertion for a fixed multiplicative constant. -/
def NaturalDensityOneFor (c : ℝ) : Prop :=
  HasNaturalDensityOne (closeDivisorSet c)

/-- The question in Erdős problem 144, with the constant `2` from the source. -/
def Question : Prop :=
  NaturalDensityOneFor 2

/-- The resolution recorded in the source: the assertion holds for every
constant strictly larger than `1`. -/
def KnownResolution : Prop :=
  ∀ c : ℝ, 1 < c → NaturalDensityOneFor c

/-- The recorded stronger resolution implies the original question. -/
theorem stronger_resolution_implies_question
    (h : KnownResolution) : Question := by
  simpa [Question] using h 2 (by norm_num)

/-- Unfolding the formalized question gives exactly the density assertion for
the source's constant `2`. -/
theorem question_spec :
    Question ↔ HasNaturalDensityOne (closeDivisorSet (2 : ℝ)) := by
  rfl

#print axioms stronger_resolution_implies_question

end Erdos144