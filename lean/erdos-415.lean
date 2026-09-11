import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-- A strict ordering pattern on `k` terms is represented by a permutation of
the `k` ranks. -/
def Appears (n k : ℕ) (p : Equiv.Perm (Fin k)) : Prop :=
  ∃ m ∈ Finset.range (n + 1),
    m + k ≤ n ∧
      ∀ i j : Fin k,
        p i < p j ↔
          Nat.totient (m + i.1 + 1) < Nat.totient (m + j.1 + 1)

/-- Every one of the `k!` strict ordering patterns appears before `n`. -/
def AllPatterns (n k : ℕ) : Prop :=
  ∀ p : Equiv.Perm (Fin k), Appears n k p

/-- The finite version of the function `F(n)` from the question. -/
def F (n : ℕ) : ℕ :=
  (Finset.filter
      (fun k => k ≤ n ∧ AllPatterns n k)
      (Finset.range (n + 1))).sup id

/-- There is a strictly decreasing string of `k` consecutive totients
starting at some admissible `m`. -/
def StrictlyDecreasing (n k : ℕ) : Prop :=
  ∃ m ∈ Finset.range (n + 1),
    m + k ≤ n ∧
      ∀ i j : Fin k,
        i.1 + 1 = j.1 →
          Nat.totient (m + i.1 + 1) > Nat.totient (m + j.1 + 1)

/-- The corresponding maximum for the decreasing pattern mentioned in the
resolution. -/
def G (n : ℕ) : ℕ :=
  (Finset.filter
      (fun k => k ≤ n ∧ StrictlyDecreasing n k)
      (Finset.range (n + 1))).sup id

/-- An occurrence whose complete comparison pattern, including equalities,
matches that of `φ(1), ..., φ(k)`. -/
def MimicsNatural (n k : ℕ) : Prop :=
  ∃ m ∈ Finset.range (n + 1),
    m + k ≤ n ∧
      ∀ i j : Fin k,
        (Nat.totient (m + i.1 + 1) < Nat.totient (m + j.1 + 1) ↔
          Nat.totient (i.1 + 1) < Nat.totient (j.1 + 1)) ∧
        (Nat.totient (m + i.1 + 1) = Nat.totient (m + j.1 + 1) ↔
          Nat.totient (i.1 + 1) = Nat.totient (j.1 + 1))

theorem witness_pos :
    Appears 2 1 (Equiv.refl (Fin 1)) := by
  refine ⟨0, by simp, by simp, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp

theorem witness_neg :
    ¬ AllPatterns 2 2 := by
  intro h
  have ha := h (Equiv.refl (Fin 2))
  rcases ha with ⟨m, hm, hbound, hcomp⟩
  have hm0 : m = 0 := by
    omega
  subst m
  have h01 := hcomp (0 : Fin 2) (1 : Fin 2)
  have hright : Nat.totient 1 < Nat.totient 2 := by
    have hleft :
        (Equiv.refl (Fin 2)) (0 : Fin 2) <
          (Equiv.refl (Fin 2)) (1 : Fin 2) := by
      norm_num
    simpa using h01.mp hleft
  have heq : Nat.totient 1 = Nat.totient 2 := by
    native_decide
  rw [heq] at hright
  exact (Nat.lt_irrefl _ hright)

/-- The first question has a negative answer: the asserted asymptotic for `F`
does not hold.  Here `IsEquivalent` formalizes the displayed
`(c + o(1)) log log log n`. -/
theorem main_conjecture :
    ¬ ∃ c : ℝ,
      Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => (F n : ℝ))
        (fun n : ℕ =>
          c * Real.log (Real.log (Real.log (n : ℝ)))) := by
  sorry

end