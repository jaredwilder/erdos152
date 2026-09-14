/- 
SOURCE (frozen), NODE n000-question (question), VERBATIM:
Can $\mathbb{N}$ be $2$-coloured such that if\[\{a,a+d,\ldots,a+(k-1)d\}\]is a $k$-term monochromatic arithmetic progression then $k\ll_\epsilon a^\epsilon$ for all $\epsilon>0$?

SOURCE (frozen), NODE n001-resolution (resolution), VERBATIM:
#984 : [Er80,p.92] arithmetic progressions | additive combinatorics A question of Spencer, who proved that this is possible with $3$ colours, with $a^\epsilon$ replaced by a very slowly growing function $h(a)$ (the inverse of the van der Waerden function). Erdős reports that he can construct such a colouring with the bound $k\ll a^{1-c}$ for some absolute constant $c>0$. He knew no non-trivial lower bound. Zach Hunter has proved the answer is yes (see the comments). Additional thanks to : Zach Hunter Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 04 April 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #984, https://www.erdosproblems.com/984, accessed 2026-08-30 From the external database . You can help update this. Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos984

/-- A monochromatic arithmetic progression for a two-colouring `c`.
The step is required to be positive, and the quantified indices are bounded
by `k`, so this predicate is decidable on every concrete instance. -/
def MonoAP (c : ℕ → Bool) (a d k : ℕ) : Prop :=
  0 < k ∧ 0 < d ∧ ∀ i < k, c (a + i * d) = c a

/-- POSITIVE WITNESS: a one-term progression satisfies `MonoAP`. -/
theorem monoAP_witness_pos :
    MonoAP (fun _ : ℕ => false) 0 1 1 := by
  decide

/-- NEGATIVE WITNESS: changing the colour at the second point destroys the
two-term progression while changing no other relevant condition. -/
theorem monoAP_witness_neg :
    ¬ MonoAP (fun x : ℕ => if x = 1 then true else false) 0 1 2 := by
  decide

/-- The bounded version of monochromaticity, restricted to progressions whose
starting point, step, and length lie below the finite bound `n`. -/
def MonoAPFinite (n : ℕ) (c : ℕ → Bool) (a d k : ℕ) : Prop :=
  0 < k ∧ 0 < d ∧ a + (k - 1) * d < n ∧
    ∀ i < k, c (a + i * d) = c a

/-- A finite colouring has no monochromatic arithmetic progression of length
at least two among the first `n` points and the bounded parameters. -/
def FiniteGood (n : ℕ) (c : ℕ → Bool) : Bool :=
  decide
    (∀ a < n, ∀ d < n, ∀ k < n + 1,
      2 ≤ k → ¬ MonoAPFinite n c a d k)

/-- POSITIVE WITNESS: the alternating colouring is good through two points. -/
theorem finiteGood_witness_pos :
    FiniteGood 2 (fun x : ℕ => if x = 0 then false else true) = true := by
  decide

/-- NEGATIVE WITNESS: the constant colouring is a near miss, failing only by
making the two points of the length-two progression have the same colour. -/
theorem finiteGood_witness_neg :
    FiniteGood 2 (fun _ : ℕ => false) = false := by
  decide

#print axioms finiteGood_witness_pos
#print axioms finiteGood_witness_neg

/-- The source question, read literally with `k ≪ε a^ε` as an eventual
constant-times-power bound. The resolution node records that the answer is yes;
the proof of this global additive-combinatorial assertion is not reproduced here. -/
theorem answer :
    ∃ c : ℕ → Bool,
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∃ A : ℕ, ∀ a d k : ℕ, A ≤ a →
            MonoAP c a d k →
              (k : ℝ) ≤ C * Real.rpow (a : ℝ) ε := by
  sorry Erdos984
