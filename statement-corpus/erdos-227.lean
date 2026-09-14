/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f=\sum_{n=0}^\infty a_nz^n$ be an entire function which is not a polynomial. Is it true that if\[\lim_{r\to \infty} \frac{\max_n\lvert a_nr^n\rvert}{\max_{\lvert z\rvert=r}\lvert f(z)\rvert}\]exists then it must be $0$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#227 : [Er57] [Er61,p.249] [Er82e] analysis Clunie (unpublished) proved this if $a_n\geq 0$ for all $n$. This was disproved in general by Clunie and Hayman [ClHa64] , who showed that the limit can take any value in $[0,1/2]$. See also [513] . Additional thanks to : Yongxi Lin Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (1) Proof claims (0) More information and links This page was last edited 06 January 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #227, https://www.erdosproblems.com/227, accessed 2026-08-30 From the external database . You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult Looks tractable Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter

-- @category research solved






open Classical Filter

namespace Erdos227

/-- The supremum of the coefficient terms `‖a n‖ r^n` at radius `r`.  The
definition uses `sSup`; all substantive uses below explicitly require
boundedness and nonemptiness of the underlying set, so its default value on
junk inputs is not being used as mathematical evidence. -/
noncomputable def coefficientMaximum (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ n : ℕ, x = ‖a n‖ * r ^ n}

/-- The supremum of `‖f z‖` on the Euclidean circle of radius `r`.  As with
`coefficientMaximum`, the boundedness and nonemptiness conditions are part of
the well-formedness data whenever this quantity is used. -/
noncomputable def circleMaximum (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- The quotient appearing in Erdős problem 227. -/
noncomputable def coefficientRatio (f : ℂ → ℂ) (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  coefficientMaximum a r / circleMaximum f r

/-- The coefficient sequence `a` is eventually zero, which is the literal
formalization of being the coefficient sequence of a polynomial. -/
def IsPolynomialCoefficients (a : ℕ → ℂ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N < n → a n = 0

/-- Data asserting that the power series with coefficients `a` defines the
entire function `f`, together with the non-polynomial condition. -/
structure EntireExpansion (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop where
  hasSum : ∀ z : ℂ, HasSum (fun n : ℕ => a n * z ^ n) (f z)
  not_polynomial : ¬ IsPolynomialCoefficients a

/-- The explicit boundedness and nonemptiness safeguards for the two suprema.
The radius restriction is `0 ≤ r`, as relevant to the limit `r → ∞`. -/
structure SupremumControl (f : ℂ → ℂ) (a : ℕ → ℂ) : Prop where
  coefficient_bdd :
    ∀ r : ℝ, 0 ≤ r →
      BddAbove {x : ℝ | ∃ n : ℕ, x = ‖a n‖ * r ^ n}
  coefficient_nonempty :
    ∀ r : ℝ, 0 ≤ r →
      Set.Nonempty {x : ℝ | ∃ n : ℕ, x = ‖a n‖ * r ^ n}
  circle_bdd :
    ∀ r : ℝ, 0 ≤ r →
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}
  circle_nonempty :
    ∀ r : ℝ, 0 ≤ r →
      Set.Nonempty {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- The literal question from the source, with the required supremum
controls made explicit.  The source clause reads: “if the limit exists then
it must be 0”; this is represented by a `Tendsto` hypothesis and conclusion. -/
def Question : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℕ → ℂ),
    EntireExpansion f a →
    SupremumControl f a →
    ∀ l : ℝ,
      Tendsto (coefficientRatio f a) atTop (𝓝 l) →
      l = 0

/-- A counterexample package formalizing the resolution: an entire,
non-polynomial expansion whose quotient has a positive limiting value in
`[0, 1/2]`. -/
structure ClunieHaymanWitness where
  f : ℂ → ℂ
  a : ℕ → ℂ
  expansion : EntireExpansion f a
  sup_control : SupremumControl f a
  limit : ℝ
  limit_mem : 0 ≤ limit ∧ limit ≤ (1 / 2 : ℝ)
  limit_positive : 0 < limit
  tends :
    Tendsto (coefficientRatio f a) atTop (𝓝 limit)

/-- The resolved mathematical input from Clunie and Hayman.  The existence
of such a witness is recorded as a named, explicit gap: formalizing their
analytic construction and proof remains to be supplied. -/
def ResolutionClaim : Prop :=
  ∃ w : ClunieHaymanWitness, True

/-- The recorded resolution supplies the counterexample witness.  Remaining
gap: formalization of the Clunie--Hayman construction showing that its
function is entire, non-polynomial, and has the asserted quotient limit. -/
theorem clunie_hayman_resolution : ResolutionClaim := by
  sorry

/-- A sequence with infinitely many nonzero coefficients cannot be the
coefficient sequence of a polynomial. -/
theorem not_polynomial_of_infinitely_many_nonzero
    (a : ℕ → ℂ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ a n ≠ 0) :
    ¬ IsPolynomialCoefficients a := by
  intro hp
  rcases hp with ⟨N, hN⟩
  rcases h N with ⟨n, hn, hne⟩
  exact hne (hN n hn)

/-- Assuming the named Clunie--Hayman resolution claim, the source's
question is false.  This follows because the source asks whether every
existing limit is zero, while the witness has a strictly positive limit.
The source-to-Lean mapping is: its “limit” is `w.limit`, its numerator and
denominator are `coefficientMaximum` and `circleMaximum`, and its
“must be 0” conclusion is exactly the conclusion in `Question`. -/
theorem question_is_false (h : ResolutionClaim) : ¬ Question := by
  rcases h with ⟨w, _⟩
  intro hq
  have hz : w.limit = 0 :=
    hq w.f w.a w.expansion w.sup_control w.limit w.tends
  linarith [w.limit_positive]

/-- The resolution claim is enough to refute the literal question. -/
theorem resolved_refutation : ¬ Question := by
  exact question_is_false clunie_hayman_resolution

#print axioms not_polynomial_of_infinitely_many_nonzero
#print axioms question_is_false
#print axioms resolved_refutation

end Erdos227
