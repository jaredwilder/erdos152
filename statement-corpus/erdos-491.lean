/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $f:\mathbb{N}\to \mathbb{R}$ be an additive function (i.e. $f(ab)=f(a)+f(b)$ whenever $(a,b)=1$). If there is a constant $c$ such that $\lvert f(n+1)-f(n)\rvert <c$ for all $n$ then must there exist some $c'$ such that\[f(n)=c'\log n+O(1)?\]
-/

/-
SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#491 : [Er61,p.237] [Er72,p.85] [Er82e,p.65] number theory Erdős [Er46] proved that if $f(n+1)-f(n)=o(1)$ or $f(n+1)\geq f(n)$ then $f(n)=c\log n$ for some constant $c$. This is true, and was proved by Wirsing [Wi70] . See also [897] and [1122] . Additional thanks to : Wouter van Doorn Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 01 April 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #491, https://www.erdosproblems.com/491, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos491

/-- A real-valued arithmetic function is additive on coprime products. -/
def IsAdditive (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b

/-- The bounded successive-difference hypothesis from the source. -/
def HasBoundedIncrement (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < c

/-- A formalization of `f(n) = c' log n + O(1)`, with the asymptotic bound
required for every positive natural number. -/
def HasLogApproximation (f : ℕ → ℝ) : Prop :=
  ∃ c' K : ℝ, 0 ≤ K ∧
    ∀ n : ℕ, 1 ≤ n →
      |f n - c' * Real.log (n : ℝ)| ≤ K

/-- The literal formalized question: every additive function with bounded
successive differences has a logarithmic approximation up to a bounded error. -/
def Problem491 : Prop :=
  ∀ f : ℕ → ℝ, IsAdditive f → HasBoundedIncrement f → HasLogApproximation f

/-- Control: the zero function satisfies the coprime-additivity definition. -/
theorem zero_isAdditive : IsAdditive (fun _ : ℕ => (0 : ℝ)) := by
  intro a b hab
  simp

/-- Control: the zero function satisfies the bounded-increment hypothesis with
constant `1`. -/
theorem zero_hasBoundedIncrement :
    HasBoundedIncrement (fun _ : ℕ => (0 : ℝ)) := by
  refine ⟨1, ?_⟩
  intro n
  simp

/-- Control: the zero function has the required logarithmic approximation, with
both constants equal to zero. -/
theorem zero_hasLogApproximation :
    HasLogApproximation (fun _ : ℕ => (0 : ℝ)) := by
  refine ⟨0, 0, le_rfl, ?_⟩
  intro n hn
  simp

/-- The resolution records this problem as true, with the underlying result
proved by Wirsing. The formal derivation of the analytic number-theoretic
result remains an explicit gap here.

The source clause asks whether bounded successive differences force
`f(n) = c' log n + O(1)`. The statement below uses exactly that reading:
`IsAdditive` formalizes additivity for coprime inputs, `HasBoundedIncrement`
formalizes the displayed uniform strict bound, and `HasLogApproximation`
formalizes the existence of `c'` and a uniform bounded error on `n ≥ 1`. -/
theorem problem491_solved : Problem491 := by
  sorry

#print axioms zero_isAdditive
#print axioms zero_hasBoundedIncrement
#print axioms zero_hasLogApproximation
#print axioms problem491_solved

end Erdos491
