import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-- The factor-difference set of a positive natural number. -/
def factorDiff (n : ℕ) : Finset ℕ :=
  Finset.image (fun a => Nat.dist a (n / a))
    ((Finset.range (n + 1)).filter (fun a => n % a = 0))

/-- The common factor-differences for a finite increasing family of positive numbers. -/
def commonDiffs {k B : ℕ} (v : Fin k → Fin B) : Finset ℕ :=
  (Finset.range (B + 1)).filter
    (fun d => ∀ i : Fin k, d ∈ factorDiff ((v i).val + 1))

/-- A bounded instance of the Erdős problem, with all selected integers positive. -/
def boundedInstance (k B : ℕ) : Prop :=
  ∃ v : Fin k → Fin B,
    (∀ i j : Fin k, i.val < j.val → (v i).val < (v j).val) ∧
      (commonDiffs v).card ≥ k

/-- The source records the cases k = 2, k = 3, and k = 4. -/
def sourceRecordedCases : Finset ℕ := {2, 3, 4}

/-- Erdős problem 885. -/
theorem erdos_885 :
    ∀ k : ℕ, 1 ≤ k → ∃ B : ℕ, boundedInstance k B := by
  sorry

theorem witness_pos : boundedInstance 1 1 := by
  let v : Fin 1 → Fin 1 := fun _ => 0
  have hmem : 0 ∈ factorDiff 1 := by
    rw [factorDiff]
    refine Finset.mem_image.mpr ⟨1, ?_, ?_⟩
    · simp
    · norm_num
  refine ⟨v, ?_, ?_⟩
  · intro i j hij
    dsimp [v]
    omega
  · apply Finset.card_pos.mpr
    refine ⟨0, ?_⟩
    change 0 ∈ (Finset.range (1 + 1)).filter
      (fun d => ∀ i : Fin 1, d ∈ factorDiff ((v i).val + 1))
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    intro i
    dsimp [v]
    exact hmem

theorem witness_neg : ¬ boundedInstance 2 1 := by
  intro h
  rcases h with ⟨v, hstrict, hcard⟩
  have hh := hstrict (0 : Fin 2) (1 : Fin 2) (by norm_num)
  have h0lt := (v (0 : Fin 2)).isLt
  have h1lt := (v (1 : Fin 2)).isLt
  have h0 : (v (0 : Fin 2)).val = 0 := by
    omega
  have h1 : (v (1 : Fin 2)).val = 0 := by
    omega
  omega

end