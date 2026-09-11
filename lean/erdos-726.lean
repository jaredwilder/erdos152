import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
-- Erdős Problem #726, [EGRS75].
-- The source refers to the interval (p/2,p) modulo p and to the
-- classical comparison with Mertens' estimate.

def residueCondition (n p : ℕ) : Prop :=
  ((Finset.range p).filter
    (fun r => p / 2 < r ∧ n % p = r % p)).Nonempty

def primeReciprocalSum (n : ℕ) : ℝ :=
  Finset.sum
    ((Finset.range (n + 1)).filter
      (fun p => Nat.Prime p ∧ residueCondition n p))
    (fun p => (1 : ℝ) / (p : ℝ))

theorem witness_pos : residueCondition 2 3 := by
  refine ⟨2, ?_⟩
  simp [residueCondition]

theorem witness_neg : ¬ residueCondition 1 3 := by
  intro h
  rcases h with ⟨r, hr⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hr
  omega

theorem erdos_problem_726 :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => primeReciprocalSum n)
      (fun n : ℕ => Real.log (Real.log (n : ℝ)) / 2) := by
  sorry

end