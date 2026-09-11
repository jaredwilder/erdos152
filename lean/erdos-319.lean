import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators

/-
  Erdős problem 319.  The elements of `Fin N` represent the integers
  `1, ..., N` by the map `x ↦ x.val + 1`.
-/

def signedSum {N : ℕ} {A : Finset (Fin N)} (δ : A → Fin 2)
    (B : Finset A) : ℚ :=
  B.sum (fun x =>
    (if δ x = (0 : Fin 2) then (-1 : ℚ) else 1) /
      ((x.1.1 + 1 : ℕ) : ℚ))

def admissible {N : ℕ} (A : Finset (Fin N)) : Prop :=
  ∃ δ : A → Fin 2,
    signedSum δ (Finset.univ : Finset A) = 0 ∧
      ∀ B : Finset A,
        B.Nonempty →
        B ≠ (Finset.univ : Finset A) →
        signedSum δ B ≠ 0

def hasSize (N k : ℕ) : Prop :=
  ∃ A : Finset (Fin N), A.card = k ∧ admissible A

def largestSize (N : ℕ) : ℕ :=
  Nat.findGreatest (hasSize N) N

theorem witness_pos : hasSize 0 0 := by
  classical
  refine ⟨∅, rfl, ?_⟩
  let δ : (∅ : Finset (Fin 0)) → Fin 2 := fun x => Fin.elim0 x.1
  refine ⟨δ, ?_, ?_⟩
  · simp [signedSum]
  · intro B hB hne
    have hB0 : B = ∅ := by
      ext x
      exact Fin.elim0 x.1
    rw [hB0] at hB
    exact False.elim (by simpa using hB)

theorem witness_neg : ¬ hasSize 1 1 := by
  classical
  rintro ⟨A, hcard, hAd⟩
  have hA : A = (Finset.univ : Finset (Fin 1)) := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  subst A
  rcases hAd with ⟨δ, hzero, _⟩
  let x0 : (Finset.univ : Finset (Fin 1)) := ⟨0, by simp⟩
  have hu :
      (Finset.univ :
        Finset (Finset.univ : Finset (Fin 1))) = {x0} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton]
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      trivial
  by_cases hd : δ x0 = (0 : Fin 2)
  · rw [hu] at hzero
    norm_num [signedSum, x0, hd] at hzero
  · rw [hu] at hzero
    norm_num [signedSum, x0, hd] at hzero

/-
  The resolution gives the asymptotic lower bound
  `(1 - 1 / e + o(1)) * N` for the largest size.
-/
theorem main_conjecture :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (1 - 1 / Real.exp 1 - ε) * (N : ℝ) ≤ (largestSize N : ℝ) := by
  sorry

end