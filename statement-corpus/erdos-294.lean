/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $N\geq 1$ and let $t(N)$ be the least integer $t$ such that there is no solution to\[1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}\]with $t=n_1<\cdots <n_k\leq N$. Estimate $t(N)$.
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#294 : [ErGr80,p.35] number theory | unit fractions Erdős and Graham [ErGr80] could show\[t(N)\ll\frac{N}{\log N},\]but had no idea of the true value of $t(N)$. Solved by Liu and Sawhney [LiSa24] (up to $(\log\log N)^{O(1)}$), who proved that\[\frac{N}{(\log N)(\log\log N)^3(\log\log\log N)^{O(1)}}\ll t(N) \ll \frac{N}{\log N}.\] Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links This page was last edited 18 November 2025. ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #294, https://www.erdosproblems.com/294, accessed 2026-08-30 From the external database . Formalised statement? No ( create one ) OEIS Possible Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical

-- @category research solved








open Classical Filter

namespace Erdos294

/-- A unit-fraction representation with strictly increasing positive-denominator
entries, whose first entry is `t` and whose entries are all at most `N`. -/
def HasUnitFractionSolution (t N : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ ns : Fin k → ℕ,
    ns 0 = t ∧
    StrictMono ns ∧
    (∀ i, ns i ≤ N) ∧
    (∑ i : Fin k, (1 : ℚ) / (ns i : ℚ)) = 1

/-- The set of candidate first denominators for which the required
unit-fraction representation does not exist. -/
def CandidateSet (N : ℕ) : Set ℕ :=
  {t : ℕ | 1 ≤ t ∧ ¬ HasUnitFractionSolution t N}

/-- The least candidate in `CandidateSet N`, formalizing the source's `t(N)`.
The use of `sInf` is safe here because the set is nonempty: `N + 1` is always a
candidate, since no entry equal to `N + 1` can be at most `N`. -/
noncomputable def tValue (N : ℕ) : ℕ :=
  sInf (CandidateSet N)

/-- The elementary anti-vacuity control: `N + 1` cannot be the first
denominator of a solution whose entries are all at most `N`. -/
theorem no_solution_after_bound (N : ℕ) :
    ¬ HasUnitFractionSolution (N + 1) N := by
  intro h
  rcases h with ⟨k, hk, ns, hfirst, _, hbound, _⟩
  have hzero := hbound (0 : Fin k)
  omega

/-- The candidate set is nonempty, so the `sInf` defining `tValue` is
not using its empty-set default. -/
theorem candidateSet_nonempty (N : ℕ) :
    (CandidateSet N).Nonempty := by
  refine ⟨N + 1, ?_⟩
  constructor
  · omega
  · exact no_solution_after_bound N

/-- The defining minimum is attained: `tValue N` is at least one and has
no unit-fraction representation with entries bounded by `N`. -/
theorem tValue_mem (N : ℕ) :
    tValue N ∈ CandidateSet N := by
  unfold tValue
  exact Nat.sInf_mem (candidateSet_nonempty N)

/-- A proved numerical control on the definition: the least forbidden
first denominator is at most `N + 1`. -/
theorem tValue_le_succ (N : ℕ) :
    tValue N ≤ N + 1 := by
  apply Nat.sInf_le
  exact show N + 1 ∈ CandidateSet N from by
    constructor
    · omega
    · exact no_solution_after_bound N

/-- A precise asymptotic reading of the Liu--Sawhney resolution.  The
unspecified implied constants are represented by positive real constants,
and the source's `(log log log N)^{O(1)}` loss is represented by an
unspecified positive real exponent.  The inequalities are required only
for `N ≥ 100`, avoiding irrelevant small-argument logarithms. -/
def LiuSawhneyBounds : Prop :=
  ∃ cLower cUpper exponent : ℝ,
    0 < cLower ∧ 0 < cUpper ∧ 0 < exponent ∧
    ∀ N : ℕ, 100 ≤ N →
      cLower * (N : ℝ) /
          (Real.log (N : ℝ) *
            (Real.log (Real.log (N : ℝ))) ^ 3 *
            (Real.log (Real.log (Real.log (N : ℝ)))) ^ exponent)
        ≤ (tValue N : ℝ) ∧
      (tValue N : ℝ) ≤ cUpper * (N : ℝ) / Real.log (N : ℝ)

/-- Liu and Sawhney's solved estimate, formalized with explicit eventual
quantifiers and constants as specified in `LiuSawhneyBounds`.  The proof
of this deep number-theoretic result remains an honest external gap. -/
theorem liu_sawhney_bounds : LiuSawhneyBounds := by
  sorry

#print axioms no_solution_after_bound
#print axioms candidateSet_nonempty
#print axioms tValue_mem
#print axioms tValue_le_succ

end Erdos294
