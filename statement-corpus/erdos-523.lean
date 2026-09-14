/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(z)=\sum_{0\leq k\leq n} \epsilon_k z^k$ be a random polynomial, where $\epsilon_k\in \{-1,1\}$ independently uniformly at random for $0\leq k\leq n$. Does there exist some constant $C>0$ such that, almost surely,\[\max_{\lvert z\rvert=1}\left\lvert \sum_{k\leq n}\epsilon_k(t)z^k\right\rvert=(C+o(1))\sqrt{n\log n}?\]
-/

/-
RESOLUTION (frozen), node `n001-resolution`, VERBATIM:
#523 : [Er61,p.253] analysis | probability | polynomials Salem and Zygmund [SaZy54] proved that $\sqrt{n\log n}$ is the right order of magnitude, but not an asymptotic. This was settled by Halász [Ha73] , who proved this is true with $C=1$. Additional thanks to : Adrian Beker Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links This page was last edited 01 February 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #523, https://www.erdosproblems.com/523, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open Filter
open scoped BigOperators

-- @category research solved







open Classical Filter

namespace Erdos523

/-- A coefficient taking the two values occurring in the source polynomial. -/
def signValue (b : Bool) : ℂ :=
  if b then 1 else -1

/-- The random-sign polynomial associated to a finite coefficient sequence. -/
def polynomial (n : ℕ) (ε : Fin (n + 1) → Bool) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.univ, signValue (ε k) * z ^ (k : ℕ)

/-- The set of absolute values of the polynomial on the complex unit circle. -/
def circleValues (n : ℕ) (ε : Fin (n + 1) → Bool) : Set ℝ :=
  {r | ∃ z : ℂ, ‖z‖ = 1 ∧ r = ‖polynomial n ε z‖}

/-- 
The supremum of the absolute value on the unit circle.  This is an `sSup`, so its
mathematical use requires nonemptiness and boundedness; those facts are proved
below, preventing the empty-set or unbounded-set default from carrying content.
-/
noncomputable def circleMaximum (n : ℕ) (ε : Fin (n + 1) → Bool) : ℝ :=
  sSup (circleValues n ε)

/-- The unit-circle value set is nonempty, by evaluating at `z = 1`. -/
theorem circleValues_nonempty (n : ℕ) (ε : Fin (n + 1) → Bool) :
    (circleValues n ε).Nonempty := by
  refine ⟨‖polynomial n ε 1‖, 1, by norm_num, rfl⟩

/-- The unit-circle values are bounded above by the number of coefficients. -/
theorem circleValues_bddAbove (n : ℕ) (ε : Fin (n + 1) → Bool) :
    BddAbove (circleValues n ε) := by
  refine ⟨(n + 1 : ℕ), ?_⟩
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  calc
    ‖polynomial n ε z‖ ≤
        ∑ k ∈ Finset.univ, ‖signValue (ε k) * z ^ (k : ℕ)‖ := by
          apply norm_sum_le
    _ = (n + 1 : ℕ) := by
          simp [polynomial, signValue, hz]

/-- A concrete sanity check: the degree-zero polynomial has absolute value one at `z = 1`. -/
theorem polynomial_zero_at_one (ε : Fin 1 → Bool) :
    polynomial 0 ε 1 = signValue (ε 0) := by
  simp [polynomial]

/-- The degree-zero circle maximum is exactly one. -/
theorem circleMaximum_zero (ε : Fin 1 → Bool) :
    circleMaximum 0 ε = 1 := by
  sorry

/--
This predicate records the almost-sure asymptotic assertion from the source.
The remaining formalisation gap is the construction of the product probability
space of independent fair signs and its almost-sure asymptotic statement.
-/
def AlmostSureAsymptotic (C : ℝ) : Prop :=
  sorry

/-- The formalised question: existence of a positive asymptotic constant. -/
def Question523 : Prop :=
  ∃ C : ℝ, 0 < C ∧ AlmostSureAsymptotic C

/--
Halász's resolution of Erdős problem 523.  The derivation is not proved here:
the missing input is the literature theorem establishing the almost-sure
asymptotic, with constant `C = 1`, together with its probability-space
formalisation.
-/
theorem halasz_resolution : Question523 := by
  sorry

#print axioms polynomial_zero_at_one

end Erdos523
