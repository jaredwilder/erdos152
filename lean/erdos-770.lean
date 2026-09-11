import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology

/-- The numbers `2^n - 1, 3^n - 1, ..., k^n - 1` are pairwise coprime. -/
def MutuallyCoprimeUpTo (n k : ℕ) : Prop :=
  ((Finset.Icc 2 k : Finset ℕ) : Set ℕ).Pairwise
    (fun a b : ℕ => Nat.Coprime (a ^ n - 1) (b ^ n - 1))

/-- The first endpoint at which the displayed sequence ceases to be mutually coprime. -/
noncomputable def h (n : ℕ) : ℕ :=
  if H : ∃ k : ℕ, ¬ MutuallyCoprimeUpTo n k then
    Nat.find H
  else
    0

/-- The assertion that the first failure occurs at `k`. -/
def FirstFailure (n k : ℕ) : Prop :=
  ¬ MutuallyCoprimeUpTo n k ∧
    ∀ j < k, MutuallyCoprimeUpTo n j

/-- Existence of a natural density for the integers whose value of `h` is `p`. -/
def DensityExists (p : ℕ) : Prop :=
  ∃ d : ℝ,
    Filter.Tendsto
      (fun N : ℕ =>
        ((Finset.filter (fun m : ℕ => h m = p) (Finset.range N)).card : ℝ) /
          (N : ℝ))
      Filter.atTop (𝓝 d)

/-- `p` is the greatest prime whose predecessor divides `n`. -/
def IsGreatestPrimeDivisor (n p : ℕ) : Prop :=
  Nat.Prime p ∧
    (p - 1) ∣ n ∧
      ∀ q : ℕ, Nat.Prime q → (q - 1) ∣ n → q ≤ p

/-- The assertion that `h` tends to infinity in the liminf sense. -/
def LiminfTendsToInfinity : Prop :=
  ∀ B : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B ≤ h n

theorem witness_pos : MutuallyCoprimeUpTo 3 3 := by
  unfold MutuallyCoprimeUpTo
  simp only [Set.Pairwise]
  rintro a ha b hb hab
  have ha_mem : a ∈ Finset.Icc 2 3 := ha
  have hb_mem : b ∈ Finset.Icc 2 3 := hb
  rcases Finset.mem_Icc.mp ha_mem with ⟨ha₂, ha₃⟩
  rcases Finset.mem_Icc.mp hb_mem with ⟨hb₂, hb₃⟩
  interval_cases a <;> interval_cases b <;> norm_num [Nat.Coprime] at *

theorem witness_neg : ¬ MutuallyCoprimeUpTo 3 4 := by
  intro hpair
  unfold MutuallyCoprimeUpTo at hpair
  simp only [Set.Pairwise] at hpair
  have hc := hpair
    (show (2 : ℕ) ∈ (Finset.Icc 2 4 : Set ℕ) by norm_num)
    (show (4 : ℕ) ∈ (Finset.Icc 2 4 : Set ℕ) by norm_num)
    (by norm_num)
  norm_num [Nat.Coprime] at hc

/-- Erdos problem 770: the density questions, the liminf question, and the
claimed characterization by the greatest prime divisor condition. -/
theorem erdos_problem_770 :
    (∀ p : ℕ, Nat.Prime p → DensityExists p) ∧
      LiminfTendsToInfinity ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ n p : ℕ,
          IsGreatestPrimeDivisor n p →
            (p : ℝ) > Real.rpow (n : ℝ) ε →
              h n = p) := by
  sorry

end