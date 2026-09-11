import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/- 
The source numerals include: 711, 1, 3, 2, 80, 92, 36, 1000, 1992,
26, 2026, 710, and 8.
-/

def HasAdmissibleTuple (n : ℕ) (m : ℤ) (L : ℕ) : Prop :=
  ∃ a : Fin n → Fin (L + 1),
    Function.Injective a ∧
      ∀ i : Fin n,
        m < m + (a i).val ∧
          m + (a i).val < m + (L : ℤ) ∧
            ((i.val + 1 : ℕ) : ℤ) ∣ (m + (a i).val)

noncomputable def f (n : ℕ) (m : ℤ) : ℕ :=
  sInf {L : ℕ | HasAdmissibleTuple n m L}

def Erdos711Claim : Prop :=
  (∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ m : ℤ, (f n m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) ∧
  (∀ B : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ m : ℤ, B ≤ f n m - f n n)

theorem witness_pos :
    HasAdmissibleTuple 2 0 3 := by
  refine ⟨![1, 2], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> norm_num

theorem witness_neg :
    ¬ HasAdmissibleTuple 2 0 2 := by
  rintro ⟨a, hinj, h⟩
  have h0 := h (⟨0, by decide⟩ : Fin 2)
  have h1 := h (⟨1, by decide⟩ : Fin 2)
  rcases h0 with ⟨h0a, h0b, h0c⟩
  rcases h1 with ⟨h1a, h1b, h1c⟩
  have heq :
      a (⟨0, by decide⟩ : Fin 2) = a (⟨1, by decide⟩ : Fin 2) := by
    apply Fin.ext
    omega
  have hne :
      (⟨0, by decide⟩ : Fin 2) ≠ (⟨1, by decide⟩ : Fin 2) := by
    decide
  exact hne (hinj heq)

theorem erdos_problem_711 : Erdos711Claim := by
  sorry

end