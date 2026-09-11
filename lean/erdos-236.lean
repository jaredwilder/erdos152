import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Erdős problem 236:
Let f(n) count the number of solutions to n = p + 2^k for prime p and k ≥ 0.
The question is whether f(n) = o(log n).
-/

/-- A pair `(p, k)` is a solution for `n = p + 2^k`. -/
def solution (n k : ℕ) : Prop :=
  (Finset.filter
      (fun p : ℕ => Nat.Prime p ∧ n = p + 2 ^ k)
      (Finset.range (n + 1))).Nonempty

/-- The number of solutions to `n = p + 2^k` with prime `p` and `k ≥ 0`. -/
def f (n : ℕ) : ℕ :=
  (Finset.filter (fun k : ℕ => solution n k) (Finset.range (n + 1))).card

/-
The restriction `k ∈ Finset.range (n + 1)` loses no solutions: whenever
`n = p + 2^k` with prime `p`, one has `k ≤ n`. The type `ℕ` incorporates
the condition `k ≥ 0` from the source.
-/

/-- The open conjecture that `f(n) = o(log n)`. -/
def Erdos236 : Prop :=
  (fun n : ℕ => (f n : ℝ)) =o[Filter.atTop]
    (fun n : ℕ => Real.log (n : ℝ))

theorem witness_pos : solution 3 0 := by
  unfold solution
  refine ⟨2, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · norm_num
  · constructor
    · norm_num
    · norm_num

theorem witness_neg : ¬ solution 3 1 := by
  intro h
  unfold solution at h
  rcases h with ⟨p, hp⟩
  rcases Finset.mem_filter.mp hp with ⟨_, ⟨hpprime, heq⟩⟩
  norm_num at heq
  have hp_eq : p = 1 := by
    omega
  subst p
  norm_num at hpprime

theorem erdos_236 : Erdos236 := by
  sorry

end