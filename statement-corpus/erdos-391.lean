/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $t(n)$ be maximal such that there is a representation\[n!=a_1\cdots a_n\]with $t(n)=a_1\leq \cdots \leq a_n$. Obtain good bounds for $t(n)/n$. In particular, is it true that\[\lim \frac{t(n)}{n}=\frac{1}{e}?\]Furthermore, does there exist some constant $c>0$ such that\[\frac{t(n)}{n} \leq \frac{1}{e}-\frac{c}{\log n}\]for infinitely many $n$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#391 : [ErGr80,p.75] [Er96b] number theory | factorials It is easy to see that\[\lim \frac{t(n)}{n}\leq \frac{1}{e}.\]Erdős [Er96b] wrote he, Selfridge, and Straus had proved a corresponding lower bound, so that $\lim \frac{t(n)}{n}=\frac{1}{e}$, and 'believed that Straus had written up our proof. Unfortunately Straus suddenly died and no trace was ever found of his notes. Furthermore, we never could reconstruct our proof, so our assertion now can be called only a conjecture.' Alladi and Grinstead [AlGr77] have obtained similar results when the $a_i$ are restricted to prime powers. Both questions were answered by Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr, and Ventullo [ACRSTUV25] , who proved that\[\frac{t(n)}{n}= \frac{1}{e}-\frac{c_0}{\log n}+O\left(\frac{1}{(\log n)^{1+c}}\right),\]where $c_0=0.3044\cdots$ is an explicit constant, for some $c>0$. They also obtain highly precise computations of $t(n)$ for many $n$, in particular establishing various explicit conjectures of Guy and Selfridge [GuSe98] , such as $t(n)\leq n/e$ for $n\neq 1,2,4$ and $t(n)\geq n/3$ for $n\geq 43632$ (and $43632$ is the best possible here). This is problem B22 of Guy's collection [Gu04] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 28 September 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #391, https://www.erdosproblems.com/391, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) OEIS A034258 , A034259 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/






-- @category research solved

import Mathlib
open Classical
open Filter
open scoped BigOperators Topology







open Classical Filter

namespace Erdos391

/-- A nondecreasing factorization of `n!` into `n` natural-number factors. -/
def IsFactorization (n : ℕ) (a : Fin n → ℕ) : Prop :=
  (∏ i, a i = n.factorial) ∧
    ∀ i j : Fin n, i ≤ j → a i ≤ a j

/-- The set of possible first factors in nondecreasing factorizations of `n!`.
The later use of `sSup` is mathematically meaningful only after boundedness
above and nonemptiness have been supplied; the corresponding control facts are
recorded below. -/
def candidateValues (n : ℕ) (hn : 0 < n) : Set ℕ :=
  {k | ∃ a : Fin n → ℕ, IsFactorization n a ∧ a ⟨0, hn⟩ = k}

/-- The maximal first factor, with the harmless convention `t 0 = 0`.
For positive `n`, this is the supremum of the actual candidate values. -/
noncomputable def t (n : ℕ) : ℕ :=
  if hn : 0 < n then sSup (candidateValues n hn) else 0

/-- The candidate set is nonempty for every positive parameter.
This is needed to rule out the empty-set default of `sSup`. -/
theorem candidateValues_nonempty (n : ℕ) (hn : 0 < n) :
    (candidateValues n hn).Nonempty := by
  sorry

/-- The candidate set is bounded above for every positive parameter.
This is needed to rule out the unbounded-set default of `sSup`. -/
theorem candidateValues_bddAbove (n : ℕ) (hn : 0 < n) :
    BddAbove (candidateValues n hn) := by
  sorry

/-- A proved sanity check: the constant one tuple is a factorization of `1!`,
and consequently `1` is an actual candidate value. -/
theorem one_is_candidate :
    1 ∈ candidateValues 1 (by decide) := by
  refine ⟨fun _ : Fin 1 => 1, ?_, ?_⟩
  · constructor
    · simp
    · intro i j hij
      simp
  · simp [candidateValues]

/-- The constant appearing in the published asymptotic expansion,
recorded to the precision displayed in the source. -/
noncomputable def c₀ : ℝ := 0.3044

/-- Formal version of the asymptotic expansion from the resolution.
The expression `O(1/(log n)^(1+c))` is represented by an eventual
absolute-value bound with a fixed constant. -/
def HasAsymptoticExpansion : Prop :=
  ∃ c C : ℝ, ∃ N : ℕ,
    0 < c ∧ 0 < C ∧ 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        |(t n : ℝ) / (n : ℝ) -
          (1 / Real.exp 1 - c₀ / Real.log (n : ℝ))| ≤
            C / (Real.log (n : ℝ)) ^ (1 + c)

/-- The source sentence is read literally as follows: `t(n)` is the
maximum first factor among nondecreasing factorizations of `n!`, and the
resolution records that the two questions have been answered by the
stated asymptotic formula. The mathematical input supplied by the cited
paper is left as an explicit honest proof gap here. -/
theorem published_asymptotic : HasAsymptoticExpansion := by
  sorry

#print axioms Erdos391.one_is_candidate
