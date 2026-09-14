/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A=\{a_1<a_2<\cdots\}\subseteq \mathbb{N}$ be infinite such that $a_{i+1}/a_i\to 1$. For any $x\geq a_1$ let\[f(x) = \frac{x-a_i}{a_{i+1}-a_i}\in [0,1),\]where $x\in [a_i,a_{i+1})$. Is it true that, for almost all $\alpha$, the sequence $f(\alpha n)$ is uniformly distributed in $[0,1)$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#492 : [Er61] [Er64b] number theory For example if $A=\mathbb{N}$ then $f(x)=\{x\}$ is the usual fractional part operator. A problem due to Le Veque [LV53] , who proved it in some special cases. Davenport and Le Veque [DaLe63] proved this under the assumption that $a_n-a_{n-1}$ is monotonic. Davenport and Erdős [DaEr63] proved it is true if $a_n \gg n^{1/2+\epsilon}$ for some $\epsilon>0$. The general conjecture is false, as shown by Schmidt [Sc69] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #492, https://www.erdosproblems.com/492, accessed 2026-08-30 From the external database . You can help update this. Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/


import Mathlib
open Classical
open Filter
open MeasureTheory
open Topology

-- @category research solved








open Classical Filter

namespace Erdos492

/-- The increasing sequence of natural numbers enumerates the set `A` occurring in the source. -/
def EnumeratedSet (a : ℕ → ℕ) : Set ℕ :=
  Set.range a

/-- 
An admissible sequence is strictly increasing, positive, infinite in range, and has
successive quotient tending to one.  The quotient is interpreted in `ℝ`.
-/
def Admissible (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
    (∀ i, 0 < a i) ∧
    Set.Infinite (EnumeratedSet a) ∧
    Tendsto (fun i : ℕ => (a (i + 1) : ℝ) / (a i : ℝ)) atTop (𝓝 1)

/-- 
The interpolation function associated with an admissible sequence.  On an interval
`[a i, a (i+1))` it is `(x-a i)/(a (i+1)-a i)`; outside all such intervals the
default value is zero.  The source only applies this function for `x ≥ a 0`.
-/
noncomputable def interpolation (a : ℕ → ℕ) (x : ℝ) : ℝ :=
  if h : ∃ i : ℕ, (a i : ℝ) ≤ x ∧ x < (a (i + 1) : ℝ) then
    (x - (a (Nat.find h) : ℝ)) /
      ((a (Nat.find h + 1) : ℝ) - (a (Nat.find h) : ℝ))
  else
    0

/-- 
Uniform distribution in `[0,1)` is expressed by convergence of the empirical
frequency in every subinterval `[p,q)` to its length.
-/
def UniformlyDistributed (u : ℕ → ℝ) : Prop :=
  ∀ p q : ℝ, 0 ≤ p → p ≤ q → q ≤ 1 →
    Tendsto
      (fun N : ℕ =>
        ((Finset.filter
            (fun n : ℕ => p ≤ u n ∧ u n < q)
            (Finset.range N)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (q - p))

/-- 
The question from the source, read literally with `a 0` in place of `a₁`.
The almost-everywhere quantifier is taken with respect to Lebesgue measure
restricted to positive real parameters, and the sequence starts at `n+1`;
this avoids the irrelevant value at zero.
-/
def Erdos492Question : Prop :=
  ∀ a : ℕ → ℕ, Admissible a →
    ∀ᵐ α ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
      UniformlyDistributed (fun n : ℕ => interpolation a (α * (n + 1)))

/-- The general conjecture recorded in the source is the proposition formalized above. -/
def GeneralConjecture : Prop :=
  Erdos492Question

/-- 
A proved sanity control for the interpolation definition: for the concrete sequence
`a i = i+1`, the fallback branch gives value zero at `x = 0` and `x = -1`.
This checks that the definition is not an unconstrained or arbitrary function.
-/
theorem interpolation_control :
    interpolation (fun i : ℕ => i + 1) 0 = 0 ∧
      interpolation (fun i : ℕ => i + 1) (-1) = 0 := by
  have h₀ :
      ¬ ∃ i : ℕ,
        (((fun j : ℕ => j + 1) i : ℕ) : ℝ) ≤ 0 ∧
          (0 : ℝ) < (((fun j : ℕ => j + 1) (i + 1) : ℕ) : ℝ) := by
    rintro ⟨i, hi, _⟩
    have hi' : (0 : ℝ) < (((fun j : ℕ => j + 1) i : ℕ) : ℝ) := by
      positivity
    linarith
  have h₁ :
      ¬ ∃ i : ℕ,
        (((fun j : ℕ => j + 1) i : ℕ) : ℝ) ≤ (-1 : ℝ) ∧
          (-1 : ℝ) < (((fun j : ℕ => j + 1) (i + 1) : ℕ) : ℝ) := by
    rintro ⟨i, hi, _⟩
    have hi' : (0 : ℝ) < (((fun j : ℕ => j + 1) i : ℕ) : ℝ) := by
      positivity
    linarith
  constructor <;> simp [interpolation, h₀, h₁]

/-- 
Resolution recorded by Schmidt: the source says that the general conjecture is false.
The proof of the counterexample is not reproduced here; this declaration is the
explicit, honest formalization gap for that literature result.
-/
theorem schmidt_resolution : ¬ GeneralConjecture := by
  sorry

#print axioms interpolation_control

end Erdos492
