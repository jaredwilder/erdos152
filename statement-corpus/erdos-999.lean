/- 
SOURCE (frozen), node `n000-question`, VERBATIM:
For any function $f:\mathbb{N}\to \mathbb{N}$ the property that, for almost all $\alpha$\[\left\lvert \alpha-\frac{p}{q}\right\rvert < \frac{f(q)}{q}\]has infinitely many solutions with $(p,q)=1$, is equivalent to\[\sum_{q\geq 1}\phi(q)\frac{f(q)}{q}=\infty.\]
-/

/-
SOURCE (frozen), node `n001-resolution`, VERBATIM:
#999 : [Er64b] number theory | diophantine approximation The Duffin-Schaeffer conjecture . It is easy to prove that the latter follows from the former. Erdős proved this in the special case when $f(q)q$ is bounded. The full conjecture was proved by Koukoulopoulos and Maynard [KoMa20] . Proof expositions (0) If you would like to contribute an exposition of a proof related to this problem, please message a moderator or leave your exposition as a comment. No proof expositions yet. Comments (0) More information and links ( View history ) When referring to this problem, please use the original sources of Erdős. If you wish to acknowledge this website, the recommended citation format is: T. F. Bloom, Erdős Problem #999, https://www.erdosproblems.com/999, accessed 2026-08-30 From the external database . Formalised statement? No ( create one )
-/


import Mathlib
open Classical
open Filter

-- @category research solved








open Classical Filter

namespace Erdos999

/-- A finite, decidable version of the coprimality and approximation condition from the source. -/
def ApproxFinite (f : ℕ → ℕ) (α : ℚ) (p q : ℕ) : Prop :=
  0 < q ∧
    |α - (p : ℚ) / q| < (f q : ℚ) / q ∧
      Nat.Coprime p q

/-- POSITIVE WITNESS: the fraction `0 / 1` approximates `0` when `f 1 = 1`. -/
theorem ApproxFinite_witness_pos :
    ApproxFinite (fun _ : ℕ => 1) 0 0 1 := by
  decide

/-- NEGATIVE WITNESS: the same instance fails only because the approximation radius is reduced to zero. -/
theorem ApproxFinite_witness_neg :
    ¬ ApproxFinite (fun _ : ℕ => 0) 0 0 1 := by
  decide

/-- A bounded finite shadow of having arbitrarily large denominators satisfying the source's condition. -/
def DFinite (f : ℕ → ℕ) (α : ℚ) (n B : ℕ) : Prop :=
  ∃ q < n, B ≤ q ∧ ∃ p < n, ApproxFinite f α p q

/-- POSITIVE WITNESS: below the bound `2`, denominator `1` supplies an approximation at `α = 0`. -/
theorem DFinite_witness_pos :
    DFinite (fun _ : ℕ => 1) 0 2 0 := by
  decide

/-- NEGATIVE WITNESS: the positive instance is changed in exactly one condition, namely `f q = 0`. -/
theorem DFinite_witness_neg :
    ¬ DFinite (fun _ : ℕ => 0) 0 2 0 := by
  decide

/-- 
The Duffin--Schaeffer theorem, formalized with real `α`.  The left side says that for
Lebesgue-almost every real `α` there are arbitrarily large coprime rational
approximants satisfying the stated inequality.  The right side expresses divergence
of the series by unbounded finite partial sums, with the index `q + 1` ranging over
the positive integers.

The frozen source says: “For any function ... the property ... for almost all `α`
... has infinitely many solutions ... is equivalent to ...”.  Thus the source's
“almost all `α`” maps to `∀ᵐ α ∂volume`, “infinitely many solutions” maps to
`∀ B, ∃ q, B ≤ q ∧ ...`, and the series condition maps to unbounded partial sums.
The deep implication supplied by Koukoulopoulos and Maynard remains outside this
formalization and is recorded honestly as a proof gap.
-/
theorem duffin_schaeffer :
    ∀ f : ℕ → ℕ,
      (∀ᵐ α : ℝ ∂MeasureTheory.volume,
        ∀ B : ℕ, ∃ q : ℕ, B ≤ q ∧
          ∃ p : ℕ,
            0 < q ∧
              |α - (p : ℝ) / q| < (f q : ℝ) / q ∧
                Nat.Coprime p q) ↔
        ∀ K : ℝ,
          ∃ N : ℕ,
            K ≤ ∑ q ∈ Finset.range N,
              (Nat.totient (q + 1) : ℝ) * (f (q + 1) : ℝ) / (q + 1) := by
  sorry

#print axioms ApproxFinite_witness_pos
#print axioms ApproxFinite_witness_neg
#print axioms DFinite_witness_pos
#print axioms DFinite_witness_neg

end Erdos999
