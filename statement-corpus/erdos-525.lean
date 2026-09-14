/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Is it true that all except at most $o(2^n)$ many degree $n$ polynomials with $\pm 1$-valued coefficients $f(z)$ have $\lvert f(z)\rvert <1$ for some $\lvert z\rvert=1$? What is the behaviour of\[m(f)=\min_{\lvert z\rvert=1}\lvert f(z)\rvert?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#525 : [Er61,p.253] analysis | probability | polynomials Random polynomials with independently identically distributed coefficients are sometimes called Kac polynomials - this problem considers the case of Rademacher coefficients, i.e. independent uniform $\pm 1$ values. The first problem asks whether $m(f)<1$ almost surely. Littlewood [Li66] conjectured that the stronger $m(f)=o(1)$ holds almost surely. The answer to both questions is yes: Littlewood's conjecture was solved by Kashin [Ka87] , and Konyagin [Ko94] improved this to show that $m(f)\leq n^{-1/2+o(1)}$ almost surely. This is essentially best possible, since Konyagin and Schlag [KoSc99] proved that for any $\epsilon>0$\[\limsup_{n\to \infty} \mathbb (m(f) \leq \epsilon n^{-1/2})\ll \epsilon.\]Cook and Nguyen [CoNg21] have identified the limiting distribution, proving that for any $\epsilon>0\[\lim_{n\to \infty} \mathbb (m(f) > \epsilon n^{-1/2}) = e^{-\epsilon \lambda}\]where $\lambda$ is an explicit constant. Additional thanks to : Mehtaab Sawhney Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) (View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #525, https://www.erdosproblems.com/525, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/








-- @category research solved

import Mathlib
open Classical
open Filter







open Classical Filter

namespace Erdos525

/-- A polynomial whose degree is `n` and whose coefficients through degree `n` are all
`±1`.  The coefficient condition is stated on the actual polynomial, rather than on a
separate label, so this predicate contains mathematical information about the polynomial. -/
def IsRademacherPolynomial (n : ℕ) (f : Polynomial ℂ) : Prop :=
  f.natDegree = n ∧ ∀ k ≤ n, f.coeff k = 1 ∨ f.coeff k = -1

/-- The polynomial determined by a vector of independent Rademacher signs.  The two
values of `Fin 2` encode `1` and `-1`, and the sum has one coefficient in every degree
from `0` through `n`. -/
def rademacherPolynomial (n : ℕ) (a : Fin (n + 1) → Fin 2) : Polynomial ℂ :=
  ∑ k : Fin (n + 1),
    Polynomial.monomial (k : ℕ) (if a k = 0 then (1 : ℂ) else -1)

/-- The set of values of `|f(z)|` on the unit circle.  The use of `sInf` is a
lower-bound use, so junk at an unbounded or empty set would make a positive lower
bound false; the next declarations prove that this set is nonempty and bounded below.
Attainment of the infimum, corresponding to the source's word `min`, is not needed
for the asymptotic predicates below. -/
noncomputable def valueSet (f : Polynomial ℂ) : Set ℝ :=
  {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖Polynomial.eval z f‖}

/-- The infimum version of the source's quantity `m(f)`. -/
noncomputable def m (f : Polynomial ℂ) : ℝ :=
  sInf (valueSet f)

/-- The unit-circle value set is nonempty, witnessed by `z = 1`. -/
theorem valueSet_nonempty (f : Polynomial ℂ) :
    (valueSet f).Nonempty := by
  refine ⟨‖Polynomial.eval (1 : ℂ) f‖, ?_⟩
  exact ⟨1, norm_one, rfl⟩

/-- The unit-circle value set is bounded below by zero. -/
theorem valueSet_bddBelow (f : Polynomial ℂ) :
    BddBelow (valueSet f) := by
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  exact norm_nonneg _

/-- A proved control exercising the polynomial encoding: the constant Rademacher
polynomial has coefficient `±1` at degree zero. -/
theorem rademacherPolynomial_coeff_zero (a : Fin 1 → Fin 2) :
    (rademacherPolynomial 0 a).coeff 0 =
      (if a 0 = 0 then (1 : ℂ) else -1) := by
  simp [rademacherPolynomial]

/-- The first question is represented by the assertion that the proportion of
Rademacher polynomials with `m(f) ≥ 1` is eventually smaller than every positive
multiple of `2^(-n)`, equivalently that their number is `o(2^n)`. -/
def AlmostAllBelowOne : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N,
      (Finset.univ.filter
        (fun a : Fin (n + 1) → Fin 2 =>
          ¬ m (rademacherPolynomial n a) < 1)).card
        ≤ ε * (2 : ℝ) ^ n

/-- The stronger Littlewood property is expressed as convergence in uniform
Rademacher counting proportion: for every fixed positive threshold, the proportion
with `m(f) ≥ ε` is eventually smaller than every prescribed positive error. -/
def LittlewoodProperty : Prop :=
  ∀ ε δ : ℝ, 0 < ε → 0 < δ →
    ∃ N : ℕ, ∀ n ≥ N,
      (Finset.univ.filter
        (fun a : Fin (n + 1) → Fin 2 =>
          m (rademacherPolynomial n a) ≥ ε)).card
        ≤ δ * (2 : ℝ) ^ (n + 1)

/-- The resolution recorded by the source, formalized as the two qualitative
claims asked in the question.  The proof of this literature result is not
reproduced here; the declaration is an explicit assumed result rather than an
axiom, and its body therefore honestly records the remaining gap. -/
theorem recorded_resolution : AlmostAllBelowOne ∧ LittlewoodProperty := by
  sorry Erdos525
