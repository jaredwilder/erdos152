import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős Problem #334.

The source asks for the best threshold f(n) such that n is a sum of two
f(n)-smooth positive integers.  We use the standard asymptotic convention
that n is restricted to n ≥ 2, and that smooth numbers are positive.

Source numerical data, retained verbatim:
#334; [Er76e,p.272] [ErGr80,p.70] [Er82d,p.55]; n^(1/3);
n^(4/(9√e)+ε); 0.2695; Problem 59; 03 April 2026; 2026-08-30.
-/

/-- A positive natural number is `k`-smooth if it has no prime divisor
strictly larger than `k`.  The finite interval suffices because every
positive divisor of `a` is at most `a`. -/
def IsSmooth (k a : ℕ) : Prop :=
  a ≠ 0 ∧
    ∀ p ∈ Finset.Icc (k + 1) a, ¬(Nat.Prime p ∧ p ∣ a)

/-- `n` has a representation as a sum of two positive `k`-smooth numbers. -/
def Represented (n k : ℕ) : Prop :=
  ∃ a ∈ Finset.range (n + 1),
    ∃ b ∈ Finset.range (n + 1),
      a + b = n ∧ IsSmooth k a ∧ IsSmooth k b

/-- A function is a valid smoothness bound for all nontrivial natural inputs. -/
def GoodBound (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → Represented n (f n)

/-- The expected subpolynomial strengthening mentioned in the source. -/
def EventuallySubpower (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (f n : ℝ) ≤ Real.rpow (n : ℝ) ε

theorem witness_pos : Represented 2 2 := by
  have hs : IsSmooth 2 1 := by
    constructor
    · norm_num
    · intro p hp
      have hp' : 3 ≤ p ∧ p ≤ 1 := by
        simpa using hp
      omega
  exact ⟨1, by simp, 1, by simp, by norm_num, hs, hs⟩

theorem witness_neg : ¬ Represented 4 1 := by
  have no2 : ¬ IsSmooth 1 2 := by
    intro h
    have hp := h.2 2 (by simp)
    norm_num at hp
  have no3 : ¬ IsSmooth 1 3 := by
    intro h
    have hp := h.2 3 (by simp)
    norm_num at hp
  intro h
  rcases h with ⟨a, ha, b, hb, hab, hsa, hsb⟩
  have ha_lt : a < 5 := by
    simpa using ha
  have hb_lt : b < 5 := by
    simpa using hb
  have ha_pos : 0 < a := Nat.pos_of_ne_zero hsa.1
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hsb.1
  interval_cases a <;> interval_cases b
  all_goals
    first
    | exact no2 hsa
    | exact no3 hsa
    | exact no2 hsb
    | exact no3 hsb
    | omega

/-- The open conjectural subpolynomial form of Erdős Problem #334. -/
theorem open_conjecture :
    ∃ f : ℕ → ℕ, GoodBound f ∧ EventuallySubpower f := by
  sorry

end