/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $\delta(n)$ denote the density of integers which are divisible by some integer in $(n,2n)$. What is the growth rate of $\delta(n)$? If $\delta_1(n)$ is the density of integers which have exactly one divisor in $(n,2n)$ then is it true that $\delta_1(n)=o(\delta(n))$?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#446 : [Er79e] [Er60] [ErGr80,p.89] [Ob1] number theory | divisors Besicovitch [Be34] proved that $\liminf \delta(n)=0$. Erdős [Er35] proved that $\delta(n)=o(1)$. Erdős [Er60] proved that $\delta(n)=(\log n)^{-\alpha+o(1)}$ where\[\alpha=1-\frac{1+\log\log 2}{\log 2}=0.08607\cdots.\]This estimate was refined by Tenenbaum [Te84] , and the true growth rate of $\delta(n)$ was determined by Ford [Fo08] who proved\[\delta(n)\asymp \frac{1}{(\log n)^\alpha(\log\log n)^{3/2}}.\]Erdős asked this at Oberwolfach in 1986, and wrote he was 'quite sure' that $\delta_1(n)=o(\delta(n))$, but that 'recent results of Tenenbaum throw some doubt on this'. Indeed, this was disproved by Ford [Fo08] , who showed more generally that if $\delta_r(n)$ is the density of integers with exactly $r$ divisors in $(n,2n)$ then $\delta_r(n)\gg_r\delta(n)$. See also [448] , [692] , and [693] . Additional thanks to : Zachary Chase and Kevin Ford Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (0) Proof claims (0) More information and links This page was last edited 04 November 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #446, https://www.erdosproblems.com/446, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A074738 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous <div
-/


import Mathlib
open Classical
open Filter Topology

-- @category research solved








open Classical Filter

namespace Erdos446

/-- The proportion of the first `N` natural numbers satisfying a predicate `P`. -/
noncomputable def densityApprox (P : ℕ → Prop) (N : ℕ) : ℝ :=
  (Finset.filter P (Finset.range N)).card / (N : ℝ)

/-- `x` is the natural density of the set defined by `P`. -/
def HasNatDensity (P : ℕ → Prop) (x : ℝ) : Prop :=
  Tendsto (fun N : ℕ => densityApprox P N) atTop (𝓝 x)

/-- A selected density, with value `0` only if the relevant density does not exist.
This choice is used only to package the source notation; the accompanying
`density_spec` theorem records the intended existence assertion. -/
noncomputable def densityOf (P : ℕ → Prop) : ℝ :=
  if h : ∃ x : ℝ, HasNatDensity P x then Classical.choose h else 0

/-- The predicate that an integer has a divisor strictly between `n` and `2n`. -/
def HasDivisorIn (n m : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

/-- The number of divisors of `m` lying strictly between `n` and `2n`. -/
noncomputable def divisorCountIn (n m : ℕ) : ℕ :=
  (Finset.filter (fun d : ℕ => n < d ∧ d < 2 * n ∧ d ∣ m)
    (Finset.range (2 * n + 1))).card

/-- The predicate that `m` has exactly `r` divisors in `(n,2n)`. -/
def HasExactlyDivisorsIn (r n m : ℕ) : Prop :=
  divisorCountIn n m = r

/-- The density denoted by `δ(n)` in the source. -/
noncomputable def delta (n : ℕ) : ℝ :=
  densityOf (HasDivisorIn n)

/-- The density denoted by `δ_r(n)` in the resolution. -/
noncomputable def deltaR (r n : ℕ) : ℝ :=
  densityOf (HasExactlyDivisorsIn r n)

/-- The density denoted by `δ₁(n)` in the question. -/
noncomputable def deltaOne (n : ℕ) : ℝ :=
  deltaR 1 n

/-- Two functions are comparable up to positive constant factors eventually. -/
def AsympAtTop (f g : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop, c * g n ≤ f n ∧ f n ≤ C * g n

/-- The little-oh relation at infinity. -/
def IsLittleOAtTop (f g : ℕ → ℝ) : Prop :=
  Tendsto (fun n : ℕ => f n / g n) atTop (𝓝 0)

/-- The exponent appearing in the recorded asymptotic formula. -/
noncomputable def alpha : ℝ :=
  1 - (1 + Real.log (Real.log 2)) / Real.log 2

/-- The growth profile recorded by Ford's theorem. -/
noncomputable def fordProfile (n : ℕ) : ℝ :=
  1 / (Real.rpow (Real.log (n : ℝ)) alpha *
    Real.rpow (Real.log (Real.log (n : ℝ))) (3 / 2 : ℝ))

/-- The density interpretation required by the source notation.
This is an explicit named hypothesis because proving existence of these
natural densities is part of the analytic number theory, not a definitional
consequence of the Lean encoding. -/
theorem density_spec (n : ℕ) :
    HasNatDensity (HasDivisorIn n) (delta n) := by
  sorry

/-- The corresponding density interpretation for exactly `r` divisors. -/
theorem densityR_spec (r n : ℕ) :
    HasNatDensity (HasExactlyDivisorsIn r n) (deltaR r n) := by
  sorry

/-- A proved sanity control: no natural number has a divisor strictly in `(1,2)`. -/
theorem no_divisor_in_one (m : ℕ) : ¬ HasDivisorIn 1 m := by
  rintro ⟨d, hd₁, hd₂, hdm⟩
  omega

/-- A proved sanity control exercising the exact-divisor definition at the
degenerate interval `(1,2)`. -/
theorem divisorCount_one (m : ℕ) : divisorCountIn 1 m = 0 := by
  unfold divisorCountIn
  have h :
      Finset.filter (fun d : ℕ => 1 < d ∧ d < 2 ∧ d ∣ m)
          (Finset.range (2 * 1 + 1)) = ∅ := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty]
    constructor
    · intro hd
      omega
    · intro hd
      contradiction
  rw [h]
  simp

/-- The formalized question: determine the eventual growth profile of `δ`
and decide whether the exactly-one-divisor density is little-oh of `δ`. -/
def Question : Prop :=
  AsympAtTop delta fordProfile ∧ IsLittleOAtTop deltaOne delta

/-- Ford's resolved growth theorem, formalized as two-sided eventual
comparison with the profile
`1 / ((log n)^alpha (log log n)^(3/2))`.
The analytic proof remains an explicit gap. -/
theorem ford_growth : AsympAtTop delta fordProfile := by
  sorry

/-- Ford's resolution disproves the proposed assertion
`δ₁(n) = o(δ(n))`. -/
theorem ford_disproof : ¬ IsLittleOAtTop deltaOne delta := by
  sorry

/-- Ford's stronger resolved statement: for every fixed number `r` of
divisors, `δ_r` is bounded below by a positive constant depending on `r`
times `δ` eventually. -/
theorem ford_lower_bound (r : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * delta n ≤ deltaR r n := by
  sorry Erdos446
