/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $p(z)=\prod_{i=1}^n (z-z_i)$ for $\lvert z_i\rvert \leq 1$. Is it true that\[\lvert\{ z: \lvert p(z)\rvert <1\}\rvert>n^{-O(1)}\](or perhaps even $>(\log n)^{-O(1)}$)?
    
NODE n001-resolution (resolution), VERBATIM:
#116 : [EHP58,p.133] [Er61,p.247] [Er82e] [Er90] [Er97c] polynomials | analysis Conjectured by Erdős, Herzog, and Piranian [EHP58] . The lower bound $\gg n^{-4}$ follows from a result of Pommerenke [Po61] . The lower bound $\gg (\log n)^{-1}$ was proved by Krishnapur, Lundberg, and Ramachandran [KLR25] . Wagner [Wa88] proves, for $n\geq 3$, the existence of such polynomials with\[\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \ll_\epsilon (\log\log n)^{-1/2+\epsilon}\]for all $\epsilon>0$. Krishnapur, Lundberg, and Ramachandran [KLR25] improved this upper bound to $\ll (\log\log n)^{-1}$. In [EHP58] they also ask to determine the polynomials which achieve the minimum possible value of this measure. Pólya [Po28] showed the upper bound\[\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \leq \pi\]always holds, and this is achieved only when the $z_i$ are identical. Additional thanks to : Boris Alexeev, Alfaiz, and Dustin Mixon Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (5) Proof claims (0) More information and links This page was last edited 24 October 2025. ( View history ) The source's question is formalized below using Lebesgue volume on $\mathbb C$ and an eventual lower bound with a fixed positive constant.
-/


-- @category research solved

import Mathlib
open Classical








open Classical Filter

namespace Erdos116

/-- The monic polynomial whose roots are the entries of `z`. -/
def rootPolynomial (n : ℕ) (z : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i ∈ (Finset.univ : Finset (Fin n)),
    (Polynomial.X - Polynomial.C (z i))

/-- The sublevel set appearing in the Erdős problem. -/
def sublevelSet (n : ℕ) (z : Fin n → ℂ) : Set ℂ :=
  {w | ‖(rootPolynomial n z).eval w‖ < 1}

/-- The Lebesgue volume of the sublevel set for a root configuration. -/
noncomputable def sublevelMeasure (n : ℕ) (z : Fin n → ℂ) : ℝ≥0∞ :=
  volume (sublevelSet n z)

/-- The scale corresponding to a power-law lower bound with exponent `A`. -/
noncomputable def powerScale (n A : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ)⁻¹) ^ A)

/-- A precise formalization of the first question in the source: uniformly over
root configurations in the closed unit disk, does the sublevel measure have a
polynomial lower bound? -/
def PowerLowerBoundQuestion : Prop :=
  ∃ A : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧
    ∀ (n : ℕ), 1 ≤ n →
      ∀ z : Fin n → ℂ,
        (∀ i, ‖z i‖ ≤ 1) →
          c * powerScale n A ≤ sublevelMeasure n z

/-- A precise version of the stronger logarithmic question, with the range
`n ≥ 2` avoiding the endpoint where `Real.log 1 = 0`. -/
def LogarithmicLowerBoundQuestion : Prop :=
  ∃ c : ℝ≥0∞, 0 < c ∧
    ∀ (n : ℕ), 2 ≤ n →
      ∀ z : Fin n → ℂ,
        (∀ i, ‖z i‖ ≤ 1) →
          c * ENNReal.ofReal ((Real.log (n : ℝ))⁻¹) ≤ sublevelMeasure n z

/-- The established Pommerenke result, recorded as an explicit hypothesis
because its analytic proof is not reproduced in this artifact. It gives the
source's stated `n⁻⁴` lower bound. -/
theorem pommerenke_lower_bound :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ (n : ℕ), 1 ≤ n →
        ∀ z : Fin n → ℂ,
          (∀ i, ‖z i‖ ≤ 1) →
            c * powerScale n 4 ≤ sublevelMeasure n z := by
  sorry

/-- The Pommerenke bound implies the first question as formalized here. -/
theorem pommerenke_answers_power_question
    (h : ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ (n : ℕ), 1 ≤ n →
        ∀ z : Fin n → ℂ,
          (∀ i, ‖z i‖ ≤ 1) →
            c * powerScale n 4 ≤ sublevelMeasure n z) :
    PowerLowerBoundQuestion := by
  rcases h with ⟨c, hc, hbound⟩
  refine ⟨4, c, hc, ?_⟩
  intro n hn z hz
  exact hbound n hn z hz

/-- The stronger logarithmic lower bound reported in the resolution,
attributed there to Krishnapur, Lundberg, and Ramachandran. Its proof is not
included here. -/
theorem krishnapur_lundberg_ramachandran_lower_bound :
    LogarithmicLowerBoundQuestion := by
  sorry

/-- A sanity check on the polynomial encoding: with one root at zero, the
polynomial is exactly `X`. -/
theorem rootPolynomial_one_zero :
    rootPolynomial 1 (fun _ : Fin 1 => (0 : ℂ)) = Polynomial.X := by
  simp [rootPolynomial]

#print axioms rootPolynomial_one_zero
#print axioms pommerenke_answers_power_question

end Erdos116
