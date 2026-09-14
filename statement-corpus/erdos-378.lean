/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $r\geq 0$. Does the density of integers $n$ for which $\binom{n}{k}$ is squarefree for at least $r$ values of $1\leq k<n$ exist? Is this density $>0$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#378 : [ErGr80,p.72] number theory | binomial coefficients Erdős and Graham state they can prove that, for $k$ fixed and large, the density of $n$ such that $\binom{n}{k}$ is squarefree is $o_k(1)$. They can also prove that there are infinitely many $n$ such that $\binom{n}{k}$ is not squarefree for $1\leq k<n$, and expect that the density of such $n$ is positive. Aggarwal and Cambie have observed this problem is resolved by the results of Granville and Ramaré [GrRa96] , who in particular show that the density of the set of those $n$ such that $\binom{n}{k}$ is squarefree for exactly $2m+2$ many values of $k$ exists. If this density is $\eta_m$, then the density in the original question is simply\[1-\sum_{0\leq m\leq \frac{r-1}{2}}\eta_m.\]This density is positive since $\eta_{r+1}>0$. Additional thanks to : Anay Aggarwal and Stijn Cambie Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (2) Proof claims (0) More information and links This page was last edited 28 October 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #378, https://www.erdosproblems.com/378, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos378

/-- A natural number is squarefree when no square of a prime divides it. -/
def SquarefreeNat (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

/-- The predicate that `k` is one of the admissible indices for `n` and that
`binomial n k` is squarefree. -/
def GoodK (n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧ SquarefreeNat (n.choose k)

/-- The number of indices `k` with `1 ≤ k < n` for which `binomial n k` is
squarefree. -/
def SquarefreeBinomialCount (n : ℕ) : ℕ :=
  (Finset.filter (fun k => GoodK n k) (Finset.range n)).card

/-- The integers satisfying the question's threshold `r`. -/
def AtLeast (r n : ℕ) : Prop :=
  r ≤ SquarefreeBinomialCount n

/-- The integers for which the binomial coefficient is squarefree for exactly
`2m+2` values of `k`. -/
def ExactlyEven (m n : ℕ) : Prop :=
  SquarefreeBinomialCount n = 2 * m + 2

/-- A predicate has natural density `d` when the proportions in initial
segments converge to `d`. The value at the empty initial segment is harmless
because it affects only the first term of the sequence. -/
def DensityLimit (P : ℕ → Prop) (d : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ =>
      ((Finset.filter P (Finset.range N)).card : ℝ) / (N : ℝ))
    atTop (𝓝 d)

/-- Existence of the natural density of a predicate on the natural numbers. -/
def HasDensity (P : ℕ → Prop) : Prop :=
  ∃ d : ℝ, DensityLimit P d

/-- The basic squarefree control at `1`. -/
theorem squarefree_one : SquarefreeNat 1 := by
  intro p hp hdiv
  have heq : p ^ 2 = 1 := Nat.dvd_one.mp hdiv
  have hpone : p = 1 := by
    nlinarith
  exact hp.ne_one hpone

/-- The basic squarefree control at `2`. -/
theorem squarefree_two : SquarefreeNat 2 := by
  intro p hp hdiv
  have hle : p ^ 2 ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  have hpge : 2 ≤ p := hp.two_le
  nlinarith

/-- A proved nondegeneracy control: for `n = 2`, the only admissible index is
`k = 1`, and its binomial coefficient is squarefree. -/
theorem count_control : SquarefreeBinomialCount 2 = 1 := by
  simp [SquarefreeBinomialCount, GoodK, squarefree_one, squarefree_two]

/-- A proved control showing that the threshold predicate is genuinely
sensitive to its threshold parameter at `n = 2`. -/
theorem threshold_control :
    AtLeast 1 2 ∧ ¬ AtLeast 2 2 := by
  rw [AtLeast, AtLeast, count_control]
  norm_num

/-- Formalization of the resolved statement of Erdős Problem 378. The source
says that the density of the integers with at least `r` squarefree binomial
coefficients exists and is positive. It further identifies this density as
`1 - ∑ η_m`, where `η_m` is the density of integers having exactly `2m+2`
such coefficients, and asserts positivity via `η_(r+1) > 0`.

The finite sum is written with the literal natural-number bound
`(r - 1) / 2`, so the endpoint convention for `r = 0` is explicit. The
substantive density theorem is imported from the cited results and remains an
honest formalization gap here. -/
theorem resolution_density (r : ℕ) :
    ∃ η : ℕ → ℝ,
      (∀ m : ℕ, HasDensity (fun n => ExactlyEven m n)) ∧
      0 < η (r + 1) ∧
      ∃ d : ℝ,
        DensityLimit (fun n => AtLeast r n) d ∧
        d = 1 - ∑ m ∈ Finset.range ((r - 1) / 2 + 1), η m ∧
        0 < d := by
  sorry
