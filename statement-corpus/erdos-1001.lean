/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
Let $S(N,A,c)$ be the measure of the set of those $\alpha\in (0,1)$ such that\[\left\lvert \alpha-\frac{x}{y}\right\rvert< \frac{A}{y^2}\]for some $N\leq y\leq cN$ and $(x,y)=1$. Does\[\lim_{N\to \infty}S(N,A,c)=f(A,c)\]exist? What is its explicit form?

SOURCE (frozen), node `n001-resolution`, VERBATIM:
#1001 : [Er64b] number theory | diophantine approximation A problem of Erdős, Szüsz, and Turán [EST58] , who proved that\[f(A,c)=\frac{12 A\log c}{\pi^2}\]when $0<A< \frac{c}{1+c^2}$, and also that if $\min(A,c)>10$ then $S(N,A,c)$ is bounded away from $0$ and $1$. The existence of this limit was proved by Kesten and Sós [KeSo66] , without a method to determine its value. Alternative, more explicit, proofs of the existence of this limit were provided independently by Boca [Bo08] and Xiong and Zaharescu [XiZa06] Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) Proof claims (0) More information and links ( View history ) ( View the LaTeX source ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #1001, https://www.erdosproblems.com/1001, accessed 2026-08-30 From the external database . (You can help update this.) Formalised statement? No ( create one ) Reactions Likes None Open to collaboration None Currently working on None Looks difficult None Looks tractable None Could be formalisable None Working on formalising None Previous Next
-/


import Mathlib
open Classical
open Filter
open MeasureTheory








open Classical Filter

namespace Erdos1001

-- @category research solved

/-- The quantity from the source: the Lebesgue measure of the set of
parameters `α ∈ (0,1)` admitting a reduced rational approximation with
denominator in `[N,cN]`. The outer-measure convention of `volume` is used
for this raw measurable-set expression. -/
noncomputable def S (N : ℕ) (A c : ℝ) : ℝ :=
  volume
    {α : ℝ |
      α ∈ Set.Ioo 0 1 ∧
        ∃ y : ℕ,
          N ≤ y ∧
            (y : ℝ) ≤ c * (N : ℝ) ∧
              ∃ x : ℕ,
                Nat.Coprime x y ∧
                  |α - (x : ℝ) / (y : ℝ)| < A / (y : ℝ) ^ 2}

/-- A bounded, decidable finite-instance version of the approximation
predicate. The denominator and numerator are both restricted to the first
`n+1` natural numbers, while the original interval and coprimality
conditions are retained. -/
def FiniteApprox (N n : ℕ) (A c α : ℚ) : Prop :=
  α ∈ Set.Ioo 0 1 ∧
    ∃ y : Fin (n + 1),
      N ≤ y.val ∧
        (y.val : ℚ) ≤ c * (N : ℚ) ∧
          0 < y.val ∧
            ∃ x : Fin (n + 1),
              x.val ≤ y.val ∧
                Nat.Coprime x.val y.val ∧
                  |α - (x.val : ℚ) / (y.val : ℚ)| <
                    A / (y.val : ℚ) ^ 2

/-- Boolean evaluation of the bounded finite predicate, making its
computational decidability explicit. -/
def FiniteApproxBool (N n : ℕ) (A c α : ℚ) : Bool :=
  decide (FiniteApprox N n A c α)

/-- POSITIVE WITNESS: denominator `2` and numerator `1` give the exact
approximation `1/2` in the permitted finite instance. -/
theorem finiteApprox_witness_pos :
    FiniteApproxBool 2 2 1 1 (1 / 2 : ℚ) = true := by
  decide

/-- NEGATIVE WITNESS: this is the same instance as the positive witness,
except that `α = 3/4` is exactly at the strict error threshold, so the
single strict approximation condition fails. -/
theorem finiteApprox_witness_neg :
    FiniteApproxBool 2 2 1 1 (3 / 4 : ℚ) = false := by
  decide

/-- The positive finite witness also proves the underlying proposition,
rather than merely its Boolean encoding. -/
theorem finiteApprox_prop_witness_pos :
    FiniteApprox 2 2 1 1 (1 / 2 : ℚ) := by
  decide

/-- The near-miss finite witness refutes the underlying proposition. -/
theorem finiteApprox_prop_witness_neg :
    ¬ FiniteApprox 2 2 1 1 (3 / 4 : ℚ) := by
  decide

/-- The existence assertion asked for in the source, as established by
Kesten and Sós and subsequently given more explicit proofs. The proof is
left as an explicit literature-dependent gap in this formalization. -/
theorem limit_exists (A c : ℝ) (hA : 0 < A) (hc : 1 < c) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => S N A c) atTop (𝓝 L) := by
  sorry

/-- The explicit Erdős--Szüsz--Turán formula recorded in the resolution:
for `0 < A < c / (1 + c^2)`, the limit of `S N A c` is
`12 * A * log c / π^2`. -/
theorem limit_eq_est_formula (A c : ℝ)
    (hA : 0 < A) (hc : 1 < c)
    (hsmall : A < c / (1 + c ^ 2)) :
    Tendsto (fun N : ℕ => S N A c) atTop
      (𝓝 (12 * A * Real.log c / Real.pi ^ 2)) := by
  sorry

#print axioms finiteApprox_witness_pos
#print axioms finiteApprox_witness_neg
#print axioms finiteApprox_prop_witness_pos
#print axioms finiteApprox_prop_witness_neg

end Erdos1001
