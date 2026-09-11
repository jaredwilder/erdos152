import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

def Smooth (P : Finset ℕ) (n : ℕ) : Prop :=
  0 < n ∧ n.primeFactors ⊆ P

def smoothNumber (P : Finset ℕ) (n : ℕ) : ℕ :=
  Nat.nth (Smooth P) n

def prefixLcm (P : Finset ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => Nat.lcm (prefixLcm P n) (smoothNumber P n)

def PrimeSet (P : Finset ℕ) : Prop :=
  ∀ p ∈ P, Nat.Prime p

def Admissible (P : Finset ℕ) : Prop :=
  2 ≤ P.card ∧ PrimeSet P

def Erdos269Series (P : Finset ℕ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (prefixLcm P (n + 1) : ℝ)

theorem witness_pos : Admissible ({2, 3} : Finset ℕ) := by
  unfold Admissible PrimeSet
  constructor
  · norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · norm_num
    · norm_num

theorem witness_neg : ¬ Admissible ({2} : Finset ℕ) := by
  intro h
  have hcard : 2 ≤ ({2} : Finset ℕ).card := h.1
  norm_num at hcard

theorem erdos_269 :
    ∀ P : Finset ℕ,
      Admissible P →
        Irrational (Erdos269Series P) := by
  sorry

end