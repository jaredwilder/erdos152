import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem #1073.  The sequence begins 25, 121, 169, 437 and is OEIS A256519.
The source also mentions Wilson's theorem and problem A2 of Guy's collection.
The page metadata mentions [HaSu02], (0), (1), 06 October 2025, and access on
2026-08-30.
-/

def FactorialCongruence (u : ℕ) : Prop :=
  ∃ n ∈ Finset.range u, u ∣ Nat.factorial n + 1

def IsValid (u : ℕ) : Prop :=
  1 < u ∧ ¬ Nat.Prime u ∧ FactorialCongruence u

def A (x : ℕ) : ℕ :=
  (Finset.filter IsValid (Finset.range x)).card

/-
The usual asymptotic notation A(x) ≤ x^{o(1)} is expressed by requiring that,
for every positive real ε, A is eventually bounded by a constant multiple of
x^ε.  The restriction 1 ≤ x avoids the irrelevant value at x = 0.
-/
def Subpolynomial (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℕ, 1 ≤ x →
        (f x : ℝ) ≤ C * Real.rpow (x : ℝ) ε

def problemNumber : ℕ := 1073

def initialSequence : List ℕ := [25, 121, 169, 437]

theorem witness_pos : IsValid 25 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  refine ⟨4, by norm_num, ?_⟩
  norm_num [Nat.factorial]

theorem witness_neg : ¬ IsValid 4 := by
  simp only [IsValid, FactorialCongruence]
  intro h
  rcases h.2.2 with ⟨n, hn, hd⟩
  have hn' : n < 4 := Finset.mem_range.mp hn
  interval_cases n <;> norm_num [Nat.factorial] at hd

theorem erdos_problem_1073 : Subpolynomial A := by
  sorry

end