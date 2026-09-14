/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $P(z)=\sum_{1\leq k\leq n}a_kz^k$ for some $a_k\in \mathbb{C}$ with $\lvert a_k\rvert=1$ for $1\leq k\leq n$. Does there exist a constant $c>0$ such that, for $n\geq 2$, we have\[\max_{\lvert z\rvert=1}\lvert P(z)\rvert \geq (1+c)\sqrt{n}?\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#230 : [Er57,p.297] [Er61,p.248] [Ha74] [Er80h,p.385] analysis | polynomials This is Problem 4.31 in [Ha74] , in which it is described as a conjecture of Erdős and Newman. The lower bound of $\sqrt{n}$ is trivial from Parseval's theorem. Körner [Ko80] constructed, for all $n\geq 2$, polynomials $P(z)=\sum_{k\leq n} a_kz^k$ with $\lvert a_k\rvert=1$ for $1\leq k\leq n$ such that, for all $z$ with $\lvert z\rvert=1$,\[(c_1-o(1))\sqrt{n} \leq \lvert P(z)\rvert \leq (c_2+o(1))\sqrt{n}\]for some absolute constants $0<c_1\leq c_2$. The answer is no (contrary to Erdős' initial guess). Kahane [Ka80] constructed 'ultraflat' polynomials $P(z)=\sum a_kz^k$ with $\lvert a_k\rvert=1$ such that\[P(z)=(1+o(1))\sqrt{n}\]uniformly for all $z\in\mathbb{C}$ with $\lvert z\rvert=1$, where the $o(1)$ term $\to 0$ as $n\to \infty$. For more details see the paper [BoBo09] of Bombieri and Bourgain and where Kahane's construction is improved to yield such a polynomial with\[P(z)=\sqrt{n}+O(n^{\frac{7}{18}}(\log n)^{O(1)})\]for all $z\in\mathbb{C}$ with $\lvert z\rvert=1$. See also [228] and [1150] . Additional thanks to : Alfaiz, Mehtaab Sawhney, and Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 23 January 2026. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #230, https://www.erdosproblems.com/230, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos230

/-- The coefficients of a polynomial indexed by `Fin n` all have complex modulus one. -/
def UnitCoefficients {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ k, ‖a k‖ = 1

/-- The unit-circle condition for a complex number. -/
def OnUnitCircle (z : ℂ) : Prop :=
  ‖z‖ = 1

/-- Evaluation of the polynomial whose coefficient indexed by `k` multiplies `z^(k+1)`.
This uses `Fin n` indexing for the source's indices `1 ≤ k ≤ n`. -/
def evalPoly (n : ℕ) (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ k : Fin n, a k * z ^ (k.val + 1)

/-- The formalized question from node `n000-question`. The displayed maximum is represented
by the existence of a point on the unit circle attaining the stated lower bound; for these
finite polynomials this is the corresponding compactness formulation. -/
def Question : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ a : Fin n → ℂ, UnitCoefficients a →
        ∃ z : ℂ, OnUnitCircle z ∧
          (1 + c) * Real.sqrt (n : ℝ) ≤ ‖evalPoly n a z‖

/-- A proved sanity control for the definitions: a one-term unit-coefficient polynomial
has modulus one at the unit-circle point `1`. -/
theorem control_one {a : Fin 1 → ℂ} (ha : UnitCoefficients a) :
    ∃ z : ℂ, OnUnitCircle z ∧ ‖evalPoly 1 a z‖ = 1 := by
  refine ⟨1, by norm_num [OnUnitCircle], ?_⟩
  simp [evalPoly, UnitCoefficients, ha]

/-- The settled answer recorded in node `n001-resolution`: no positive constant gives the
uniform lower bound in `Question`. This is the external mathematical result; its proof,
including the ultraflat-polynomial construction, remains to be formalized. -/
theorem resolution_no : ¬ Question := by
  sorry

#print axioms control_one
#print axioms resolution_no

end Erdos230
