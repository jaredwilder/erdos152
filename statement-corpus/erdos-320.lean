/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $S(N)$ count the number of distinct sums of the form $\sum_{n\in A}\frac{1}{n}$ for $A\subseteq \{1,\ldots,N\}$. Estimate $S(N)$.

NODE n001-resolution (resolution), VERBATIM:
#320 : [ErGr80,p.43] number theory | unit fractions Bleicher and Erdős [BlEr75] proved the lower bound\[\log S(N)\geq \frac{N}{\log N}\left(\log 2\prod_{i=3}^k\log_iN\right),\]valid for $k\geq 4$ and $\log_kN\geq k$, and also [BlEr76b] proved the upper bound\[\log S(N)\leq \frac{N}{\log N}\left(\log_r N \prod_{i=3}^r\log_iN\right),\]valid for $r\geq 1$ and $\log_{2r}N\geq 1$. (In these bounds $\log_in$ denotes the $i$-fold iterated logarithm.) Bettin, Grenié, Molteni, and Sanna [BGMS25] improved the lower bound to\[\log S(N) \geq \frac{N}{\log N}\left(2\log 2\left(1-\frac{3/2}{\log_kN}\right)\prod_{i=3}^k\log_iN\right),\]valid for $k\geq 4$ and $\log_kN\geq 3/2$. (In particular this goes to infinity faster than the lower bound of Bleicher and Erdős.) GPT 5.6 Sol (prompted by Young, Zhu, and Luo) proved an upper bound of the same order of magnitude (using the same iterative upper bound of [BlEr76b] ), and thus\[\log S(N) \asymp \frac{N}{\log N}\prod_{j=3}^k\log_j N,\]where $t$ is chosen such that $\log_k N=O(1)$. See the proof claims and associated comments for more details and the proof. See also [321] . Additional thanks to : Boris Alexeev, Dustin Mixon, and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (2) More information and links This page was last edited 16 July 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #320, https://www.erdosproblems.com/320, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A072207 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos320

/-- The set of denominators occurring in the unit fractions with indices at most `N`. -/
def unitDenominators (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- The set of distinct rational sums of reciprocals over subsets of `unitDenominators N`. -/
def subsetUnitSums (N : ℕ) : Finset ℚ :=
  (unitDenominators N).powerset.image
    (fun A => ∑ n ∈ A, (1 : ℚ) / (n : ℚ))

/-- `S N` is the number of distinct sums of the form
`∑ n ∈ A, 1 / n` for subsets `A` of `{1, ..., N}`. -/
def S (N : ℕ) : ℕ :=
  (subsetUnitSums N).card

/-- The iterated logarithm, with zeroth iterate equal to the input. -/
noncomputable def iteratedLog : ℕ → ℕ → ℝ
  | 0, N => N
  | k + 1, N => Real.log (iteratedLog k N)

/-- The product of the iterated logarithms appearing in the recorded bounds. -/
noncomputable def iteratedLogProduct (k N : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 3 k, iteratedLog i N

/-- The improved lower-bound expression recorded in the resolution. -/
noncomputable def improvedLowerTerm (k N : ℕ) : ℝ :=
  (N : ℝ) / Real.log N *
    (2 * Real.log 2 * (1 - (3 / 2 : ℝ) / iteratedLog k N) *
      iteratedLogProduct k N)

/-- The iterative upper-bound expression recorded in the resolution. -/
noncomputable def iterativeUpperTerm (r N : ℕ) : ℝ :=
  (N : ℝ) / Real.log N *
    (iteratedLog r N * iteratedLogProduct r N)

/-- The literal improved lower bound from the recorded resolution, formalized
using the iterated logarithm defined above. -/
def ImprovedLowerBound : Prop :=
  ∀ k N : ℕ, 4 ≤ k →
    (3 / 2 : ℝ) ≤ iteratedLog k N →
      improvedLowerTerm k N ≤ Real.log (S N : ℝ)

/-- The literal iterative upper bound from the recorded resolution, formalized
using the iterated logarithm defined above. -/
def IterativeUpperBound : Prop :=
  ∀ r N : ℕ, 1 ≤ r →
    (1 : ℝ) ≤ iteratedLog (2 * r) N →
      Real.log (S N : ℝ) ≤ iterativeUpperTerm r N

/-- The recorded resolution, consisting of the improved lower bound and the
iterative upper bound. The analytic estimates themselves remain an external
literature input in this formalization. -/
def RecordedResolution : Prop :=
  ImprovedLowerBound ∧ IterativeUpperBound

/-- A proved control showing that the definition is nontrivial at the empty
initial interval: there is exactly one subset sum when `N = 0`. -/
theorem S_zero : S 0 = 1 := by
  simp [S, subsetUnitSums, unitDenominators]

/-- A proved control showing that the number of distinct subset sums is always
at least one, since the empty subset contributes a sum. -/
theorem one_le_S (N : ℕ) : 1 ≤ S N := by
  unfold S subsetUnitSums
  have hnonempty :
      ((unitDenominators N).powerset.image
        (fun A => ∑ n ∈ A, (1 : ℚ) / (n : ℚ))).Nonempty := by
    refine ⟨∑ n ∈ (∅ : Finset ℕ), (1 : ℚ) / (n : ℚ), ?_⟩
    exact Finset.mem_image.mpr ⟨∅, by simp, rfl⟩
  have hpos :
      0 < ((unitDenominators N).powerset.image
        (fun A => ∑ n ∈ A, (1 : ℚ) / (n : ℚ))).card :=
    Finset.card_pos.mpr hnonempty
  omega

/-- A proved elementary upper control: distinct subset sums cannot outnumber
the subsets from which they are obtained. -/
theorem S_le_power_two (N : ℕ) :
    S N ≤ 2 ^ (unitDenominators N).card := by
  unfold S subsetUnitSums
  calc
    ((unitDenominators N).powerset.image
        (fun A => ∑ n ∈ A, (1 : ℚ) / (n : ℚ))).card
        ≤ (unitDenominators N).powerset.card := Finset.card_image_le
    _ = 2 ^ (unitDenominators N).card := Finset.card_powerset

/-- The analytic bounds in `RecordedResolution` are the settled resolution
reported by the source. Their proof is not reproduced here; it remains an
explicit honest gap rather than an asserted axiom. -/
theorem recorded_resolution : RecordedResolution := by
  sorry

#print axioms S_zero
#print axioms one_le_S
#print axioms S_le_power_two

end Erdos320
