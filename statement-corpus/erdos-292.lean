/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $A$ be the set of $n\in \mathbb{N}$ such that there exist $1\leq m_1<\cdots <m_k=n$ with $\sum\tfrac{1}{m_i}=1$. Explore $A$. In particular, does $A$ have density $1$?
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#292 : [ErGr80,p.35] number theory | unit fractions Straus observed that $A$ is closed under multiplication. Furthermore, it is easy to see that $A$ does not contain any prime power. The answer is yes, as proved by Martin [Ma00] , who in fact proved that if $B=\mathbb{N}\backslash A$ then, for all large $x$,\[\frac{\lvert B\cap [1,x]\rvert}{x}\asymp \frac{\log\log x}{\log x},\]and also gave an essentially complete description of $B$ as those integers which are small multiples of prime powers. van Doorn has observed that if $n\in A$ (with $n>1$) then $2n\in A$ also, since if $\sum \frac{1}{m_i}=1$ then $\frac{1}{2}+\sum \frac{1}{2m_i}=1$ also. Additional thanks to : Zach Hunter, Wouter van Doorn and Desmond Weisenberg Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. Comments (0) Proof claims (0) More information and links This page was last edited 20 December 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #292, https://www.erdosproblems.com/292, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) OEIS A092671 Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos292

/-- The set `A` from the source: `n ∈ A` when `n` is the final member of a
strictly increasing positive sequence of natural numbers whose reciprocal sum is
one. The reciprocals are interpreted in `ℚ`. -/
def A : Set ℕ :=
  {n | ∃ k : ℕ, ∃ m : Fin (k + 1) → ℕ,
    StrictMono m ∧
    (∀ i, 0 < m i) ∧
    m (Fin.last k) = n ∧
    (∑ i : Fin (k + 1), (1 : ℚ) / (m i : ℚ)) = 1}

/-- The endpoint sanity check `1 ∈ A`, witnessed by the one-term unit fraction
`1/1`. -/
theorem one_mem_A : 1 ∈ A := by
  refine ⟨0, (fun _ => 1), ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have ha : a.val < 1 := a.isLt
    have hb : b.val < 1 := b.isLt
    have hab' : a.val < b.val := by
      change a.val < b.val at hab
      exact hab
    omega
  · intro i
    norm_num
  · norm_num
  · norm_num

/-- A nontrivial sanity check: `6 ∈ A`, witnessed by
`1/2 + 1/3 + 1/6 = 1`. -/
theorem six_mem_A : 6 ∈ A := by
  refine ⟨2, ![2, 3, 6], ?_, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num at hab ⊢
  · intro i
    fin_cases i <;> norm_num
  · norm_num
  · norm_num [Fin.sum_univ_succ]

/-- The first structural fact recorded in the resolution: `A` is closed under
multiplication. This declaration records the settled result; its proof is not
reconstructed here. -/
theorem A_closed_mul {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) : a * b ∈ A := by
  sorry

/-- The complement-counting function used to express the density question.
The interval starts at `1`, matching the source's positive natural numbers. -/
noncomputable def complementCount (x : ℕ) : ℕ :=
  (Finset.filter (fun n => n ∉ A ∧ n ≤ x) (Finset.Icc 1 x)).card

/-- The counting function for `A` itself, again on the interval `[1,x]`. -/
noncomputable def acount (x : ℕ) : ℕ :=
  (Finset.filter (fun n => n ∈ A ∧ n ≤ x) (Finset.Icc 1 x)).card

/-- Martin's settled answer to the density question, formalized here as its
density-one consequence. The resolution gives the stronger estimate
`|B ∩ [1,x]|/x ≍ log log x/log x`; this theorem deliberately records only the
consequence that the density of `A` is one. -/
theorem A_has_density_one :
    Tendsto (fun x : ℕ => (acount x : ℝ) / (x : ℝ)) atTop (𝓝 1) := by
  sorry

/-- Equivalent complement formulation of the density-one answer. The stronger
two-sided asymptotic estimate stated in the source is not asserted by this
weaker formalization. -/
theorem complement_has_density_zero :
    Tendsto (fun x : ℕ => (complementCount x : ℝ) / (x : ℝ)) atTop (𝓝 0) := by
  sorry Erdos292

#print axioms Erdos292.one_mem_A
#print axioms Erdos292.six_mem_A
