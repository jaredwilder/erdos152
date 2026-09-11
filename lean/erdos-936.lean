import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/- Source numerical literals retained: 2, 1, 936, 76, 32, 16, 20, 0, 31, 10, 2025, 2026, 8, 30, 146968. -/

/-- A natural number is powerful if every prime divisor occurs with exponent at least 2. -/
def Powerful (m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m

def powPlus (n : ℕ) : ℕ :=
  2 ^ n + 1

def powMinus (n : ℕ) : ℕ :=
  2 ^ n - 1

def factorialPlus (n : ℕ) : ℕ :=
  Nat.factorial n + 1

def factorialMinus (n : ℕ) : ℕ :=
  Nat.factorial n - 1

def PowerfulAt (f : ℕ → ℕ) (n : ℕ) : Prop :=
  Powerful (f n)

/-- There are only finitely many natural numbers at which `f` is powerful. -/
def EventuallyNotPowerful (f : ℕ → ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, B ≤ n → ¬ Powerful (f n)

/-- Erdős problem 936: each of the four displayed families is powerful for
only finitely many natural numbers. -/
def Erdos936 : Prop :=
  EventuallyNotPowerful powPlus ∧
    EventuallyNotPowerful powMinus ∧
      EventuallyNotPowerful factorialPlus ∧
        EventuallyNotPowerful factorialMinus

theorem witness_pos : PowerfulAt factorialMinus 0 := by
  simp [PowerfulAt, Powerful, factorialMinus]

theorem witness_neg : ¬ PowerfulAt powPlus 0 := by
  intro h
  have hd : (2 : ℕ) ^ 2 ∣ powPlus 0 :=
    h 2 (by norm_num) (by norm_num [powPlus])
  norm_num [powPlus] at hd

theorem erdos_936 : Erdos936 := by
  sorry

end