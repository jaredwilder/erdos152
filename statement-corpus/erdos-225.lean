/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let\[ f(\theta) = \sum_{0\leq k\leq n}c_k e^{ik\theta}\]be a trigonometric polynomial all of whose roots are real, such that $\max_{\theta\in [0,2\pi]}\lvert f(\theta)\rvert=1$. Then\[\int_0^{2\pi}\lvert f(\theta)\rvert \mathrm{d}\theta \leq 4.\]

NODE n001-resolution (resolution), VERBATIM:
#225 : [Er40b,p.957] [Er57] [Er61,p.248] [Ha74] analysis This is Problem 4.20 in [Ha74] , where it is attributed to Erdős. This was solved independently by Kristiansen [Kr74] (only in the case when $c_k\in\mathbb{R}$) and Saff and Sheil-Small [SaSh74] (for general $c_k\in\mathbb{C}$). (The original proof of Kristiansen contained an error which was later fixed in [Kr76] .) Additional thanks to : Alfaiz, Winston Heap, Vjekoslav Kovac, and Karlo Lelas Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (1) Proof claims (0) More information and links This page was last edited 05 March 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #225, https://www.erdosproblems.com/225, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/







import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos225

/-- The algebraic polynomial whose coefficients define the trigonometric polynomial. -/
def algebraicPolynomial {n : ℕ} (c : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (n + 1), Polynomial.C (c k) * Polynomial.X ^ k.1

/-- The trigonometric polynomial
`∑ k, c k * exp (I * k * θ)`, with real parameter `θ`. -/
def trigEval {n : ℕ} (c : Fin (n + 1) → ℂ) (θ : ℝ) : ℂ :=
  ∑ k : Fin (n + 1),
    c k * Complex.exp (Complex.I * (k.1 : ℂ) * (θ : ℂ))

/-- Every complex zero of the associated algebraic polynomial is real. -/
def AllRootsReal {n : ℕ} (c : Fin (n + 1) → ℂ) : Prop :=
  ∀ z : ℂ, Polynomial.eval z (algebraicPolynomial c) = 0 → z.im = 0

/-- The maximum condition, unpacked as boundedness by `1` on `[0, 2π]`
together with attainment of the value `1`. -/
def HasMaxNormOne {n : ℕ} (c : Fin (n + 1) → ℂ) : Prop :=
  (∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) →
    ‖trigEval c θ‖ ≤ 1) ∧
  (∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
    ‖trigEval c θ‖ = 1)

/-- A proved computational control: the constant trigonometric polynomial
with coefficient `1` evaluates to `1` at the origin. -/
theorem trigEval_zero_control :
    trigEval (n := 0) (fun _ => (1 : ℂ)) 0 = 1 := by
  simp [trigEval]

/-- Erdős Problem #225.  The source clause says that a trigonometric
polynomial with real roots and maximum modulus `1` has integral at most `4`.
Here “all roots are real” is represented by `AllRootsReal`, using the
associated algebraic polynomial, and the maximum is represented by
`HasMaxNormOne`.  The restriction `0 < n` and the nonzero leading
coefficient express that `n` is the degree of the polynomial rather than
the degenerate constant case.  The proof of the solved result remains to
be formalized from the cited literature. -/
theorem erdos225
    (n : ℕ)
    (hn : 0 < n)
    (c : Fin (n + 1) → ℂ)
    (hlead : c ⟨n, Nat.lt_succ_self n⟩ ≠ 0)
    (hroots : AllRootsReal c)
    (hmax : HasMaxNormOne c) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigEval c θ‖) ≤ 4 := by
  sorry

#print axioms trigEval_zero_control

end Erdos225
