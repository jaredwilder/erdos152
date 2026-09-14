/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\alpha \in \mathbb{R}$ be irrational and $\epsilon>0$. Are there positive integers $x,y,z$ such that\[\lvert x^2+y^2-z^2\alpha\rvert <\epsilon?\]

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#496 : [Er61] number theory | diophantine approximation Originally a conjecture due to Oppenheim. Davenport and Heilbronn [DaHe46] solve the analogous problem for quadratic forms in 5 variables. This is true, and was proved by Margulis [Ma89] . Additional thanks to : Zachary Chase Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #496, https://www.erdosproblems.com/496, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos496

/-- The real-number predicate expressing irrationality by exclusion of rational values. -/
def IrrationalReal (α : ℝ) : Prop :=
  ∀ q : ℚ, α ≠ (q : ℝ)

/-- The source's approximation property, with positive natural numbers representing positive
integers and with the Euclidean quadratic expression interpreted in `ℝ`. -/
def QuadraticApproximation (α ε : ℝ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧
    0 < y ∧
    0 < z ∧
    |(x : ℝ)^2 + (y : ℝ)^2 - (z : ℝ)^2 * α| < ε

/-- A proved control for the definitions: whenever the error from the single choice
`x = y = z = 1` is below `ε`, the corresponding approximation property holds. -/
theorem one_one_one_control (α ε : ℝ)
    (h : |(2 : ℝ) - α| < ε) :
    QuadraticApproximation α ε := by
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  change |(1 : ℝ)^2 + (1 : ℝ)^2 - (1 : ℝ)^2 * α| < ε
  have hcalc :
      (1 : ℝ)^2 + (1 : ℝ)^2 - (1 : ℝ)^2 * α = 2 - α := by
    ring
  rw [hcalc]
  exact h

/-- Margulis's resolution of the source question, formalized as the assertion that every
irrational real `α` admits positive integer solutions for every positive tolerance `ε`.
The source records this result as proved by Margulis; the formal derivation from that theorem
remains an explicit gap here. -/
theorem margulis_resolution :
    ∀ α : ℝ, IrrationalReal α → ∀ ε : ℝ, 0 < ε → QuadraticApproximation α ε := by
  sorry Erdos496
