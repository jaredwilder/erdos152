import Mathlib


noncomputable section
open scoped BigOperators
/-
  Erdős Problem 33.  The use of `ℕ → Bool` makes membership decidable while
  still representing a subset of the natural numbers.
-/

def problemNumber : ℕ := 33

def FiniteSquareComplement (A : Finset ℕ) (B : ℕ) : Prop :=
  ∀ m ∈ Finset.Icc 1 B,
    ∃ n ∈ Finset.range (B + 1), ∃ a ∈ A, n * n + a = m

theorem witness_pos :
    FiniteSquareComplement ({0, 1, 2, 3} : Finset ℕ) 3 := by
  intro m hm
  have hm' : 1 ≤ m ∧ m ≤ 3 := by
    simpa only [Finset.mem_Icc] using hm
  refine ⟨0, by simp, m, ?_, by simp⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem witness_neg :
    ¬ FiniteSquareComplement ({0} : Finset ℕ) 2 := by
  intro h
  have hm : (2 : ℕ) ∈ Finset.Icc 1 2 := by simp
  rcases h 2 hm with ⟨n, hn, a, ha, heq⟩
  have ha0 : a = 0 := by simpa using ha
  subst a
  have hnlt : n < 3 := by simpa using hn
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> norm_num at heq

def AdditiveComplement (A : ℕ → Bool) : Prop :=
  ∀ᶠ m in Filter.atTop,
    ∃ n a : ℕ, 0 ≤ n ∧ A a = true ∧ n * n + a = m

def countingFunction (A : ℕ → Bool) (N : ℕ) : ℕ :=
  (Finset.filter (fun k => A k = true) (Finset.Icc 1 N)).card

def normalizedCountingFunction (A : ℕ → Bool) (N : ℕ) : ℝ :=
  (countingFunction A N : ℝ) / Real.sqrt (N : ℝ)

def LiminfAtLeast (A : ℕ → Bool) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c - ε ≤ normalizedCountingFunction A n

def LimsupAtMost (A : ℕ → Bool) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      normalizedCountingFunction A n ≤ c + ε

def optimalLimsup : ℝ :=
  sInf {c : ℝ | ∃ A : ℕ → Bool, AdditiveComplement A ∧ LimsupAtMost A c}

def moserBound : ℝ := 1.06

def bestKnownLowerBound : ℝ := 4 / Real.pi

def decimalLowerBound : ℝ := 1.273

def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

def vanDoornBound : ℝ :=
  2 * goldenRatio ^ (5 / 2)

def decimalUpperBound : ℝ := 6.66

/-
  This records the known content of the problem: additive complements exist
  with finite upper asymptotic bound, while every additive complement has the
  stated lower bounds.  Determining the exact optimal limsup remains the
  open part of the problem.
-/
theorem erdos_problem_33 :
    (∃ A : ℕ → Bool,
      AdditiveComplement A ∧ ∃ c : ℝ, LimsupAtMost A c) ∧
    (∀ A : ℕ → Bool,
      AdditiveComplement A → LiminfAtLeast A bestKnownLowerBound) ∧
    (∀ A : ℕ → Bool,
      AdditiveComplement A → LiminfAtLeast A moserBound) := by
  sorry

end