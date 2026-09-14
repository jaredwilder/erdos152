/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $f(n)\to \infty$ as $n\to \infty$. Is it true that\[\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}\]is irrational?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#270 : [ErGr80,p.66] irrationality Erdős and Graham write 'the answer is almost surely in the affirmative if $f(n)$ is assumed to be nondecreasing'. Even the case $f(n)=n$ is unknown, although Hansen [Ha75] has shown that\[\sum_n \frac{1}{\binom{2n}{n}}=\sum_n \frac{n!}{(n+1)\cdots (n+n)}=\frac{1}{3}+\frac{2\pi}{3^{5/2}}\]is transcendental. Crmarić and Kovač [CrKo25] have shown that the answer to this question is no in a strong sense: for any $\alpha \in (0,\infty)$ there exists a function $f:\mathbb{N}\to\mathbb{N}$ such that $f(n)\to \infty$ as $n\to\infty$ and\[\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}=\alpha.\]It is still possible that this sum is always irrational if $f$ is assumed to be non-decreasing; Crmarić and Kovač show that the set of the possible values of such a sum has Lebesgue measure zero. Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (3) Proof claims (0) More information and links This page was last edited 28 September 2025. ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #270, https://www.erdosproblems.com/270, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A073016 Reactions Likes Vjeko_Kovac Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open BigOperators

-- @category research solved








open Classical Filter

namespace Erdos270

/-- The condition that a natural-valued function tends to infinity. -/
def TendsToInfinity (f : ℕ → ℕ) : Prop :=
  ∀ B : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B ≤ f n

/-- The `n`-th summand, with the original sum indexed over `n ≥ 1`. -/
def summand (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  if 1 ≤ n then
    (∏ k ∈ Finset.range (f n), ((n + 1 + k : ℕ) : ℝ))⁻¹
  else
    0

/-- The real value of the series associated to a function `f`. -/
noncomputable def series (f : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, summand f n

/-- Rationality of a real number, expressed by equality with the coercion of a rational. -/
def IsRationalReal (x : ℝ) : Prop :=
  ∃ q : ℚ, x = (q : ℝ)

/-- The question asks whether every function tending to infinity gives an irrational series. -/
def Question : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f → ¬ IsRationalReal (series f)

/-- A basic control showing that the summand definition has the intended empty-product value. -/
theorem summand_one_zero_control (f : ℕ → ℕ) (h : f 1 = 0) :
    summand f 1 = 1 := by
  simp [summand, h]

/-- Crmarić and Kovač's stated strong negative resolution: every positive real target
is attained by some function tending to infinity. This is recorded as an external
literature result; its proof remains formalization work. -/
theorem exists_function_for_target (α : ℝ) (hα : 0 < α) :
    ∃ f : ℕ → ℕ, TendsToInfinity f ∧ series f = α := by
  sorry

/-- The question has a negative answer: choosing the positive rational target `1` in
the externally recorded result gives a function whose series is rational. -/
theorem answer_no : ¬ Question := by
  intro hQ
  obtain ⟨f, hf, hs⟩ := exists_function_for_target (1 : ℝ) (by norm_num)
  apply hQ f hf
  refine ⟨(1 : ℚ), ?_⟩
  simpa [hs]

#print axioms summand_one_zero_control
#print axioms answer_no

end Erdos270
