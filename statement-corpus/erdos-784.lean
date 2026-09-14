/- 
SOURCE (frozen), node `n000-question` (question), VERBATIM:
Let $C>0$. Does there exist a $c>0$ (depending on $C$) such that, for all sufficiently large $x$, if $A\subseteq [1,x]$ has $\sum_{n\in A}\frac{1}{n}\leq C$ then\[\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}\gg\frac{x}{(\log x)^c}?\]

SOURCE (frozen), node `n001-resolution` (resolution), VERBATIM:
#784 : [Er72] [Er73] [Er80,p.110] number theory An example of Schinzel and Szekeres [ScSz59] shows that this would be best possible (up to the value of $c$). See also [542] . In the comments jif has noted that the answer is trivially no for every $C\geq 1$ with $A=\{1\}$. Presumably (as is usual in these kind of questions) the assumption that $1\not\in A$ is intended. jif also notes that a lower bound of $(1-C)x$ is trivial by the union bound if $0<C<1$. Let $H_C(x)$ be the minimum value of\[\#\{ m\leq x : a\nmid m\textrm{ for all }a\in A\}\]as $A$ ranges over all subsets of $\{2,\ldots,\lfloor x\rfloor\}$ with $\sum_{n\in A}\frac{1}{n}\leq C$, so that this question asks whether\[H_C(x)\gg \frac{x}{(\log x)^{O_C(1)}}\]for all $C>0$. For $C=1$ it is known that\[H_1(x)\asymp \frac{x}{\log x}.\]The lower bound is due to Ruzsa [Ru82] , and the upper bound is due to Saias [Sa98] . More precise estimates (including a conjectured asymptotic formula of $\sim c\frac{x}{\log x}$ for an explicit $c\approx 0.878$) are given by Weingartner [We25] . For fixed $C>1$ Ruzsa answered this question in the negative. (In [Er80] Erdős states that Ruzsa's construction shows his 'intuition completely misled' him.) In fact\[H_C(x)=x^{e^{1-C}+o(1)}.\]This was improved by Weingartner [We25] who proved (for any fixed $C>1$)\[H_C(x)\asymp \frac{x^{e^{1-C}}}{\log x}.\]Together these answer the given question (positively for $0<C\leq 1$ and negatively for $C>1$). On the other hand, if $A$ is restricted to sets of primes then Erdős and Ruzsa [ErRu80] proved that there are always $\gg_C x$ many $n\leq x$ not divisible by any $p\in A$. Additional thanks to : KoishiChan and jif Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (2) Proof claims (0) More information and links This page was last edited 08 April 2026. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #784, https://www.erdosproblems.com/784, accessed 2026-08-30 From the external database . You can help update this. Formalised statement? No ( create one ) Reactions Likes jif Open to collaboration jif Currently working on jif Looks difficult None Looks tractable None Could be formalisable None Working on formalising None
-/





import Mathlib
open Classical

-- @category research solved







open Classical Filter

namespace Erdos784

/-- The reciprocal mass of a finite set of positive integers. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (n : ℝ)⁻¹

/-- `admissible C x A` expresses the source's restriction
that `A` is a subset of `{2, ..., floor x}` and has reciprocal mass at most `C`. -/
def admissible (C : ℝ) (x : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 x ∧ reciprocalMass A ≤ C

/-- The number of integers `m` in `[1,x]` divisible by none of the elements of `A`. -/
def survivorCount (x : ℕ) (A : Finset ℕ) : ℕ :=
  (Finset.filter (fun m => ∀ a ∈ A, ¬ a ∣ m) (Finset.Icc 1 x)).card

/-- The source's lower-bound assertion, with `d` as the implicit positive
constant represented by the notation `≫`. -/
def polylogLowerBound (C : ℝ) : Prop :=
  ∃ d c : ℝ, 0 < d ∧ 0 < c ∧
    ∃ K : ℕ, ∀ x : ℕ, K ≤ x →
      ∀ A : Finset ℕ, admissible C x A →
        (survivorCount x A : ℝ) ≥
          d * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) c

/-- The question in the source, formalized as a proposition rather than
asserted as a theorem. -/
def question : Prop :=
  ∀ C : ℝ, 0 < C → polylogLowerBound C

/-- The resolution's positive range: the source records this as known for
`0 < C ≤ 1`. The proof is not reproduced here. -/
theorem positive_range (C : ℝ) (hC : 0 < C) (hC1 : C ≤ 1) :
    polylogLowerBound C := by
  sorry

/-- The resolution's negative range: the source records that for every fixed
`C > 1`, the proposed polylogarithmic lower bound fails. The proof is not
reproduced here. -/
theorem negative_range (C : ℝ) (hC : 1 < C) :
    ¬ polylogLowerBound C := by
  sorry

/-- A proved control showing that the survivor-count definition is not
vacuous: with no forbidden divisors and `x = 1`, the sole integer `1` survives. -/
theorem survivorCount_one_empty :
    survivorCount 1 (∅ : Finset ℕ) = 1 := by
  simp [survivorCount]

/-- A proved control showing that the admissible-family domain is nonempty for
every positive budget, using the empty set at `x = 1`. -/
theorem admissible_one_empty {C : ℝ} (hC : 0 < C) :
    admissible C 1 (∅ : Finset ℕ) := by
  simp [admissible, reciprocalMass, le_of_lt hC]

end Erdos784

#print axioms Erdos784.survivorCount_one_empty
#print axioms Erdos784.admissible_one_empty
