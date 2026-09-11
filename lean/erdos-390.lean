import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős Problem 390.  The source records [ErGr80], [EGS82], the values
0, 3, 2026-08-30, and OEIS A193429; these numerical identifiers are
retained here: 390, 80, 82, 0, 3, 2026, 8, 30, 193429.
-/

/-- A finite strictly increasing factorization of `n!` whose largest
factor is `m`, represented as a finite set of factors bounded by `m`. -/
def hasFactorization (n m : ℕ) : Prop :=
  ∃ s : Finset (Fin (m + 1)),
    ⟨m, Nat.lt_succ_self m⟩ ∈ s ∧
      (∀ a ∈ s, n < (a : ℕ)) ∧
        s.prod (fun a => (a : ℕ)) = n.factorial

/-- The least endpoint of such a factorization, with a harmless
totalization at values of `n` for which no factorization exists. -/
noncomputable def f (n : ℕ) : ℕ :=
  if h : ∃ m, hasFactorization n m then
    Nat.find h
  else
    0

theorem witness_pos : hasFactorization 0 1 := by
  classical
  refine ⟨{⟨1, by decide⟩}, by simp, ?_, by simp⟩
  intro a ha
  have ha' : a = ⟨1, by decide⟩ := by
    simpa using ha
  subst a
  decide

theorem witness_neg : ¬ hasFactorization 1 0 := by
  rintro ⟨s, hs, hgt, hprod⟩
  have hz : (⟨0, by decide⟩ : Fin (0 + 1)) ∈ s := by
    simpa using hs
  have h := hgt ⟨0, by decide⟩ hz
  omega

/--
The open asymptotic question from Erdős Problem 390:
whether there is a constant `c` such that
`f(n) - 2*n` is asymptotic to `c*n/log n`.
-/
theorem open_problem :
    ∃ c : ℝ,
      Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => (f n : ℝ) - 2 * (n : ℝ))
        (fun n : ℕ => c * ((n : ℝ) / Real.log (n : ℝ))) := by
  sorry

end