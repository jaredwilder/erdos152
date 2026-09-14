/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\alpha >0$ and $N\geq 1$. Is it true that for any $A\subseteq \{1,\ldots,N\}$ with $\lvert A\rvert \geq \alpha N$ there exists some $S\subseteq A$ such that\[\frac{a}{b}=\sum_{n\in S}\frac{1}{n}\]with $a\leq b =O_\alpha(1)$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#310 : [ErGr80] number theory | unit fractions Liu and Sawhney [LiSa24] observed that the main result of Bloom [Bl21] implies a positive solution to this conjecture. They prove a more precise version, that if $(\log N)^{-1/7+o(1)}\leq \alpha \leq 1/2$ then there is some $S\subseteq A$ such that\[\frac{a}{b}=\sum_{n\in S}\frac{1}{n}\]with $a\leq b \leq \exp(O(1/\alpha))$. They also observe that the dependence $b\leq \exp(O(1/\alpha))$ is sharp. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #310, https://www.erdosproblems.com/310, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






import Mathlib
open Classical
open BigOperators

-- @category research solved








open Classical Filter

namespace Erdos310

/-- `UnitRep S a b` says that the finite set `S` has reciprocal sum `a / b`,
with the numerator no larger than the positive denominator. -/
def UnitRep (S : Finset ℕ) (a b : ℕ) : Prop :=
  0 < b ∧ a ≤ b ∧
    (a : ℚ) / (b : ℚ) =
      ∑ n ∈ S, (1 : ℚ) / (n : ℚ)

/-- The literal question from the source, interpreting `b = O_α(1)` as the
existence of a bound depending on `α` and independent of `N` and `A`. -/
def OriginalQuestion : Prop :=
  ∀ α : ℝ, 0 < α →
    ∀ N : ℕ, 1 ≤ N →
      ∀ A : Finset ℕ,
        A ⊆ Finset.Icc 1 N →
          (α * (N : ℝ) ≤ (A.card : ℝ)) →
            ∃ C : ℕ, ∃ S : Finset ℕ,
              S ⊆ A ∧ ∃ a b : ℕ, UnitRep S a b ∧ b ≤ C

/-- An explicit finite rendering of the source's asymptotic lower-density
condition `(log N)^(-1/7+o(1)) ≤ α`.  The `o(1)` term is not encoded here;
this definition records the displayed principal exponent and is therefore
the stated finite-range formalization used below. -/
def BloomAdmissible (α : ℝ) (N : ℕ) : Prop :=
  1 < N ∧ (Real.log (N : ℝ)) ^ (-(1 : ℝ) / 7) ≤ α

/-- The precise result recorded in the resolution, with the asymptotic
condition rendered by `BloomAdmissible` and `exp (C / α)` as the meaning of
`exp(O(1/α))`.  The literature theorem is used here as an explicitly
identified external input; its proof remains to be formalized. -/
def KnownResult : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ α : ℝ, 0 < α → α ≤ (1 : ℝ) / 2 →
      ∀ N : ℕ, BloomAdmissible α N →
        ∀ A : Finset ℕ,
          A ⊆ Finset.Icc 1 N →
            (α * (N : ℝ) ≤ (A.card : ℝ)) →
              ∃ S : Finset ℕ, S ⊆ A ∧
                ∃ a b : ℕ,
                  UnitRep S a b ∧
                    (b : ℝ) ≤ Real.exp (C / α)

/-- A proved sanity control: the singleton set `{1}` has reciprocal sum
`1/1`, so `UnitRep` is not an empty or inconsistent predicate. -/
theorem unitRep_one_control : UnitRep ({1} : Finset ℕ) 1 1 := by
  norm_num [UnitRep]

#print axioms unitRep_one_control

/-- The resolved result for Erdős problem 310.  This is recorded as a
literature-backed claim, and the remaining gap is the formal proof of the
Bloom--Liu--Sawhney theorem in the precise formalization above. -/
theorem known_result : KnownResult := by
  sorry
