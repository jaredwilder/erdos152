/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $a_n\in \mathbb{R}$ be such that $\sum_n \lvert a_n\rvert^2=\infty$ and $\lvert a_n\rvert=o(1/\sqrt{n})$. Is it true that, for almost all $\epsilon_n=\pm 1$, there exists some $z$ with $\lvert z\rvert=1$ (depending on the choice of signs) such that\[\sum_n \epsilon_n a_n z^n\]converges?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#527 : [Er61,p.254] analysis | probability It is unclear to me whether Erdős also intended to assume that $\lvert a_{n+1}\rvert\leq \lvert a_n\rvert$. It is 'well known' that, for almost all $\epsilon_n=\pm 1$, the series diverges for almost all $\lvert z\rvert=1$ (assuming only $\sum \lvert a_n\rvert^2=\infty$). Dvoretzky and Erdős [DE59] showed that if $\lvert a_n\rvert >c/\sqrt{n}$ then, for almost all $\epsilon_n=\pm 1$, the series diverges for all $\lvert z\rvert=1$. This is true, and was proved by Michelen and Sawhney [MiSa25] , who in fact proved that the set of such $z$ has Hausdorff dimension $1$. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links ( View history ) (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter
open MeasureTheory

-- @category research solved








open Classical Filter

namespace Erdos527

/-- A sign sequence assigns one of the two signs to every natural-number index. -/
abbrev SignSequence := ℕ → Fin 2

/-- The two signs associated with the two elements of `Fin 2`. -/
def signValue (b : Fin 2) : ℂ :=
  if b = 0 then 1 else -1

/-- 
The Bernoulli product probability measure on sign sequences.

The measure-theoretic construction of the product of the uniform measures on `Fin 2`
is not reproduced here; this declaration is an explicit honest gap in the present
formalization, rather than an opaque proposition parameter.
-/
noncomputable def signMeasure : Measure SignSequence := by
  sorry

/-- The property that the signed power series converges at some point of the unit circle. -/
def GoodSeries (a : ℕ → ℝ) (ε : SignSequence) : Prop :=
  ∃ z : ℂ,
    Complex.abs z = 1 ∧
      Summable (fun n : ℕ => signValue (ε n) * (a n : ℂ) * z ^ n)

/-- 
The assertion that almost every sign sequence admits a point of convergence on the
unit circle.  Here `∀ᵐ` is taken with respect to the Bernoulli product measure on
the independent signs.
-/
def AlmostEverywhereConvergence (a : ℕ → ℝ) : Prop :=
  ∀ᵐ ε ∂signMeasure, GoodSeries a ε

/-- 
A proved anti-vacuity control: the zero coefficient sequence satisfies the formalized
almost-everywhere convergence property, since the resulting series is identically zero.
This does not prove the Erdos problem, but checks that the definitions are not
accidentally impossible at a degenerate input.
-/
theorem zero_control :
    AlmostEverywhereConvergence (fun _ : ℕ => 0) := by
  unfold AlmostEverywhereConvergence
  filter_upwards [] with ε
  refine ⟨1, ?_, ?_⟩
  · norm_num
  · simp [signValue]

/-- 
Formalization of Erdos problem 527.

The source clause says that, for almost all choices of signs, there exists a
unit-modulus complex number depending on those signs at which the signed power
series converges.  The hypotheses encode
`∑ n, |a n|² = ∞` as failure of summability of the nonnegative squared sequence,
and encode `|a n| = o(1 / sqrt n)` using `IsLittleO` at `atTop`.

The source resolution records this assertion as true, with a proof attributed to
Michelen and Sawhney [MiSa25].  The theorem below therefore records the settled
mathematical claim, while its proof remains an explicit gap in this formalization.
-/
theorem erdos_527 :
    ∀ a : ℕ → ℝ,
      ¬ Summable (fun n : ℕ => |a n| ^ 2) →
      IsLittleO a (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop →
      AlmostEverywhereConvergence a := by
  sorry Erdos527
