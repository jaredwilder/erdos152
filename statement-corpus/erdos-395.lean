/-
SOURCE (frozen), node `n000-question`, VERBATIM:
If $z_1,\ldots,z_n\in \mathbb{C}$ with $\lvert z_i\rvert=1$ then is it true that the probability that\[\lvert \epsilon_1z_1+\cdots+\epsilon_nz_n\rvert \leq \sqrt{2},\]where $\epsilon_i\in \{-1,1\}$ uniformly at random, is $\gg 1/n$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#395 : [Er45] analysis A reverse Littlewood-Offord problem . Erdős originally asked this with $\sqrt{2}$ replaced by $1$, but Carnielli and Carolino [CaCa11] observed that this is false, choosing $z_1=1$ and $z_k=i$ for $2\leq k\leq n$, where $n$ is even, since then the sum is at least $\sqrt{2}$ always. Solved in the affirmative by He, Juškevičius, Narayanan, and Spiro [HJNS24] . The bound of $1/n$ is the best possible, as shown by taking $z_k=1$ for $1\leq k\leq n/2$ and $z_k=i$ otherwise. See also [498] . Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #395, https://www.erdosproblems.com/395, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising DanielChin Previous Next
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos395

/-- The signs used in the uniform random choice: `false` represents `-1` and
`true` represents `1`. -/
def signValue (b : Bool) : ℂ :=
  if b then 1 else -1

/-- The signed sum associated with a family of unit complex numbers and a
choice of signs. -/
def signedSum (n : ℕ) (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i, signValue (ε i) * z i

/-- The predicate that the signed sum lies in the disk of radius `√2`. -/
def isGoodSign (n : ℕ) (z : Fin n → ℂ) (ε : Fin n → Bool) : Prop :=
  ‖signedSum n z ε‖ ≤ Real.sqrt 2

/-- The finite set of sign choices for which the reverse Littlewood-Offord
event occurs. -/
def goodSigns (n : ℕ) (z : Fin n → ℂ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (isGoodSign n z)

/-- The probability of the small-ball event under independent uniform signs.
The denominator is the cardinality `2^n` of the sign space. -/
noncomputable def smallBallProbability (n : ℕ) (z : Fin n → ℂ) : ℝ :=
  (goodSigns n z).card / (2 : ℝ) ^ n

/-- The hypothesis that all complex numbers in the family have modulus one. -/
def UnitInputs (n : ℕ) (z : Fin n → ℂ) : Prop :=
  ∀ i, ‖z i‖ = 1

/-- The probability defined above is always nonnegative. This is a proved
control exercising the actual event-count definition. -/
theorem probability_nonnegative (n : ℕ) (z : Fin n → ℂ) :
    0 ≤ smallBallProbability n z := by
  unfold smallBallProbability
  positivity

/-- One-term control: for the unit input `z₀ = 1`, both possible signs have
modulus `1`, hence the small-ball probability is exactly `1`. -/
theorem one_term_control :
    smallBallProbability 1 (fun _ : Fin 1 => (1 : ℂ)) = 1 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h : (0 : ℝ) ≤ 2 := by norm_num
    have hsq := Real.sq_sqrt h
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hε (ε : Fin 1 → Bool) :
      isGoodSign 1 (fun _ : Fin 1 => (1 : ℂ)) ε := by
    cases h : ε 0 <;>
      simp [isGoodSign, signedSum, signValue, h, hsqrt]
  have hf :
      goodSigns 1 (fun _ : Fin 1 => (1 : ℂ)) =
        (Finset.univ : Finset (Fin 1 → Bool)) := by
    ext ε
    simp [goodSigns, hε ε]
  simp [smallBallProbability, hf]

/-- The affirmative resolution of the source question. In the source notation,
`A ≫ B` is formalized as the existence of an absolute positive constant `c`
such that `c / n ≤ A` for every positive `n`.

SOURCE-to-Lean mapping: the source asks for the probability of
`|ε₁z₁ + ⋯ + εₙzₙ| ≤ √2`, with each `|zᵢ| = 1` and uniformly random signs.
`UnitInputs` expresses the unit-modulus condition, `goodSigns` counts exactly
the favorable sign functions, and `smallBallProbability` divides by the full
sign-space cardinality `2^n`. The resolution records this statement as solved
in the affirmative by [HJNS24]. The proof remains an explicit literature gap. -/
theorem reverse_littlewood_offord :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (z : Fin n → ℂ),
        UnitInputs n z →
        0 < n →
        c / (n : ℝ) ≤ smallBallProbability n z := by
  sorry

#print axioms probability_nonnegative
#print axioms one_term_control

end Erdos395
