/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(z)$ be an entire function, not a polynomial. Does there exist a locally rectifiable path $C$ tending to infinity such that, for every $\lambda>0$, the integral\[\int_C \lvert f(z)\rvert^{-\lambda} \mathrm{d}z\]is finite?
-/

/- 
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#515 : [Er61,p.249] [Er82e] analysis Huber [Hu57] proved that for every $\lambda>0$ there is such a path $C_\lambda$ such that this integral is finite. This is true. The case when $f$ has finite order was proved by Zhang [Zh77] . The general case was proved by Lewis, Rossi, and Weitsman [LRW84] , who in fact proved this with $\lvert f\rvert$ replaced by $e^u$ where $u$ is any subharmonic function. Additional thanks to : Cedric Pilatte, Mark Sellke, and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (2) Proof claims (0) More information and links This page was last edited 19 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #515, https://www.erdosproblems.com/515, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos515

/-- A complex entire function, formalized as a function differentiable over `ℂ` at every
point. -/
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

/-- A function is non-polynomial when it is not the evaluation function of any complex
polynomial. -/
def IsNonPolynomial (f : ℂ → ℂ) : Prop :=
  ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z

/-- The path condition used below.  Local rectifiability is represented by the stronger,
directly inspectable condition of being locally Lipschitz; the path is parametrized on
`[0,∞)` and tends to infinity in the Euclidean metric on `ℂ`. -/
def IsAdmissiblePath (γ : ℝ → ℂ) : Prop :=
  Continuous γ ∧
    Tendsto (fun t : ℝ => ‖γ t‖) atTop atTop ∧
    ∀ T : ℝ, ∃ K : ℝ, LipschitzOnWith K γ (Set.Icc 0 T)

/-- Finiteness of the path integral in this formalization.  Since a general line-integral
API is not assumed here, the integral is represented by the Lebesgue integrability of
the nonnegative integrand in the chosen path parameter. -/
def HasFinitePathIntegral (f : ℂ → ℂ) (γ : ℝ → ℂ) (λ : ℝ) : Prop :=
  IntegrableOn (fun t : ℝ => Real.rpow ‖f (γ t)‖ (-λ)) (Set.Ici 0)

/-- The question in Erdos problem 515: one admissible path should work simultaneously for
all positive exponents. -/
def Erdos515Question : Prop :=
  ∀ f : ℂ → ℂ,
    IsEntire f →
    IsNonPolynomial f →
    ∃ γ : ℝ → ℂ,
      IsAdmissiblePath γ ∧
        ∀ λ : ℝ, 0 < λ → HasFinitePathIntegral f γ λ

/-- The result explicitly recorded in the resolution, with the path allowed to depend on
the positive exponent as `C_λ`.  This is kept separate from the stronger single-path
formulation in `Erdos515Question`. -/
def ResolutionResult : Prop :=
  ∀ f : ℂ → ℂ,
    IsEntire f →
    IsNonPolynomial f →
    ∀ λ : ℝ, 0 < λ →
      ∃ γ : ℝ → ℂ,
        IsAdmissiblePath γ ∧ HasFinitePathIntegral f γ λ

/-- The literature result recorded in the source, namely the existence of a path for each
positive exponent.  The analytic theorem itself remains an explicit honest gap. -/
theorem resolution_result :
    ResolutionResult := by
  sorry

/-- The single-path question implies the exponent-by-exponent resolution result.  This is a
proved logical control showing that the two formalized statements are not being conflated. -/
theorem question_implies_resolution
    (h : Erdos515Question) : ResolutionResult := by
  intro f hf hnp λ hλ
  obtain ⟨γ, hγ, hfinite⟩ := h f hf hnp
  exact ⟨γ, hγ, hfinite λ hλ⟩

#print axioms question_implies_resolution

end Erdos515
