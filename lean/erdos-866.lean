import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def intervalElement (N : ℕ) (x : Fin (2 * N)) : ℕ :=
  x.val + 1

def boundedValue (N : ℕ) (x : Fin (4 * N + 1)) : ℤ :=
  (x.val : ℤ) - (2 * N : ℕ)

def sumIn (N : ℕ) (A : Finset (Fin (2 * N))) (s : ℤ) : Prop :=
  ∃ x : Fin (2 * N), (x.val : ℤ) + 1 = s ∧ x ∈ A

def hasConfiguration (k N : ℕ) (A : Finset (Fin (2 * N))) : Prop :=
  ∃ b : Fin k → Fin (4 * N + 1),
    ∀ i j : Fin k, i ≠ j →
      sumIn N A (boundedValue N (b i) + boundedValue N (b j))

def good (k N t : ℕ) : Prop :=
  ∀ A : Finset (Fin (2 * N)),
    A.card ≥ N + t →
      hasConfiguration k N A

theorem good_sufficient (k N : ℕ) : good k N (N + 1) := by
  intro A hA
  have hcard : A.card ≤ 2 * N := by
    simpa using (Finset.card_le_univ A)
  exfalso
  omega

def g (k N : ℕ) : ℕ :=
  Nat.find (p := good k N) ⟨N + 1, good_sufficient k N⟩

theorem witness_pos : good 3 1 2 := by
  intro A hA
  have hcard : A.card ≤ 2 * 1 := by
    simpa using (Finset.card_le_univ A)
  exfalso
  omega

theorem witness_neg : ¬ good 3 1 0 := by
  intro h
  let A : Finset (Fin 2) := {(0 : Fin 2)}
  have hA : A.card ≥ 1 := by
    simp [A]
  obtain ⟨b, hb⟩ := h A hA
  have extract : ∀ {s : ℤ}, sumIn 1 A s → s = 1 := by
    intro s hs
    rcases hs with ⟨x, hx, hxm⟩
    have hx0 : x = (0 : Fin 2) := by
      simpa [A] using hxm
    subst x
    norm_num at hx
    exact hx.symm
  have h01 :=
    extract (hb (0 : Fin 3) (1 : Fin 3) (by decide))
  have h02 :=
    extract (hb (0 : Fin 3) (2 : Fin 3) (by decide))
  have h12 :=
    extract (hb (1 : Fin 3) (2 : Fin 3) (by decide))
  dsimp [boundedValue] at h01 h02 h12
  omega

def asymptoticUpper : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N →
        (g k N : ℝ) ≤
          C * Real.rpow (N : ℝ) (1 - Real.rpow (1 / 2 : ℝ) k)

def largeKLower : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        Real.rpow (N : ℝ) (1 - ε) < (g k N : ℝ)

def logarithmicFive : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ N : ℕ, 2 ≤ N →
      c * Real.log (N : ℝ) ≤ (g 5 N : ℝ) ∧
        (g 5 N : ℝ) ≤ C * Real.log (N : ℝ)

def squareRootSix : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ N : ℕ, 1 ≤ N →
      c * Real.sqrt (N : ℝ) ≤ (g 6 N : ℝ) ∧
        (g 6 N : ℝ) ≤ C * Real.sqrt (N : ℝ)

theorem resolution_claims :
    (∀ N : ℕ, 1 ≤ N → g 3 N = 2) ∧
    (∀ N : ℕ, 1 ≤ N → g 4 N ≤ 2032) ∧
    logarithmicFive ∧
    squareRootSix ∧
    asymptoticUpper ∧
    largeKLower := by
  sorry

end