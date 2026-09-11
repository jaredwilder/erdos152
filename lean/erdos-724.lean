import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Source data: Erdos problem #724 [Er81]. Euler's conjecture concerned
n ≡ 2 mod 4; Bose, Parker, and Shrikhande [BPS60] proved f(n) ≥ 2
for n ≥ 7. Earlier bounds were n^(1/91) [CES60], n^(1/17) [Wi74],
and n^(1/14.8) [Be83c]. The sequence is OEIS A001438.
The source citation date is 2026-08-30.
-/

def LatinSquare (n : ℕ) := Fin n → Fin n → Fin n

def IsLatin (n : ℕ) (L : LatinSquare n) : Prop :=
  (∀ r : Fin n, ∀ c₁ c₂ : Fin n, L r c₁ = L r c₂ → c₁ = c₂) ∧
  (∀ c : Fin n, ∀ r₁ r₂ : Fin n, L r₁ c = L r₂ c → r₁ = r₂)

def Orthogonal (n : ℕ) (L M : LatinSquare n) : Prop :=
  ∀ r s : Fin n, ∀ c d : Fin n,
    (r, c) ≠ (s, d) → L r c = L s d → M r c ≠ M s d

def HasMOLS (n k : ℕ) : Prop :=
  ∃ F : Fin k → LatinSquare n,
    (∀ i : Fin k, IsLatin n (F i)) ∧
    (∀ i j : Fin k, i ≠ j → F i ≠ F j ∧ Orthogonal n (F i) (F j))

theorem hasMOLS_zero (n : ℕ) : HasMOLS n 0 := by
  refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

def f (n : ℕ) : ℕ := by
  let S := (Finset.range (n + 1)).filter (fun k => HasMOLS n k)
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S, hasMOLS_zero]
  exact S.max' hS

theorem witness_pos : HasMOLS 1 1 := by
  refine ⟨(fun _ _ _ => 0), ?_, ?_⟩
  · intro i
    constructor
    · intro r c₁ c₂ h
      exact Subsingleton.elim _ _
    · intro c r₁ r₂ h
      exact Subsingleton.elim _ _
  · intro i j hij
    exfalso
    exact hij (Subsingleton.elim _ _)

theorem witness_neg : ¬ HasMOLS 1 2 := by
  intro h
  rcases h with ⟨F, hLatin, hdistinct⟩
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by
    intro h
    have hv : (0 : ℕ) = 1 := congrArg (fun x : Fin 2 => x.val) h
    omega
  have hne : F (0 : Fin 2) ≠ F (1 : Fin 2) :=
    (hdistinct (0 : Fin 2) (1 : Fin 2) h01).1
  apply hne
  funext r c
  exact Subsingleton.elim _ _

def Erdos724Conjecture : Prop :=
  ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧
    ∀ n : ℕ, N ≤ n → C * Real.sqrt (n : ℝ) ≤ (f n : ℝ)

theorem erdos_724_conjecture : Erdos724Conjecture := by
  sorry

end