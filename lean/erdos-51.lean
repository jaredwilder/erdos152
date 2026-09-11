import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Frozen source, Erdos problem 51:

Is there an infinite set A ⊆ ℕ such that for every a ∈ A there is an integer n
such that φ(n) = a, and yet if n_a is the smallest such integer then
n_a / a → ∞ as a → ∞?

#51 : [Er95] [Er98] number theory Carmichael has asked whether there is an
integer t for which φ(n)=t has exactly one solution. Erdős has proved that if
such a t exists then there must be infinitely many such t. See also [694].
This is discussed in problems B36 and B39 of Guy's collection [Gu04].
Proof expositions (0) Comments (9) Proof claims (0)
This page was last edited 30 September 2025.
accessed 2026-08-30
OEIS A002202, A014197
-/

/-- Existence of a natural-number preimage under Euler's totient function.
    Natural numbers encode the positive integers occurring in the question. -/
def HasTotientPreimage (a : ℕ) : Prop :=
  ∃ n : ℕ, Nat.totient n = a

/-- The least natural-number preimage, when one exists. -/
noncomputable def leastPreimage (a : ℕ) : ℕ :=
  if h : HasTotientPreimage a then Nat.find h else 0

/--
The exact Erdos problem 51 predicate.

The limit is taken along the subtype of elements of `A`; its `atTop` filter
formalizes `a → ∞` within `A`.
-/
def erdosProblem51 : Prop :=
  ∃ A : Set ℕ,
    A.Infinite ∧
    (∀ a : ℕ, a ∈ A → HasTotientPreimage a) ∧
    Filter.Tendsto
      (fun x : {a : ℕ // a ∈ A} =>
        (leastPreimage x.1 : ℝ) / (x.1 : ℝ))
      Filter.atTop Filter.atTop

/--
A decidable finite approximation: all values in `A` are bounded by `N`,
their least preimages are witnessed below `N^2`, and the corresponding
preimage-to-value ratio is at least `N`.
-/
def finiteApprox (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A,
    a ≤ N ∧
      ∃ m ≤ N ^ 2,
        Nat.totient m = a ∧
          (∀ k ≤ N ^ 2, Nat.totient k = a → m ≤ k) ∧
          N * a ≤ m

theorem witness_pos : finiteApprox 1 ({1} : Finset ℕ) := by
  intro a ha
  have ha' : a = 1 := by simpa using ha
  subst a
  refine ⟨by norm_num, 1, by norm_num, by norm_num, ?_, by norm_num⟩
  intro k hk hk_eq
  have hk0 : k ≠ 0 := by
    intro hk0
    subst k
    norm_num at hk_eq
  omega

theorem witness_neg : ¬ finiteApprox 2 ({1} : Finset ℕ) := by
  intro h
  have h1 := h 1 (by simp)
  rcases h1 with ⟨_, m, hm, htot, hmin, hratio⟩
  have hm1 := hmin 1 (by norm_num) (by norm_num)
  omega

theorem erdos_problem_51 : erdosProblem51 := by
  sorry

end