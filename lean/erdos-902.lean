import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def IsTournament (m : Nat) (r : Fin m → Fin m → Bool) : Prop :=
  (∀ a, r a a = false) ∧
    (∀ a b, a ≠ b → (r a b = true ↔ r b a = false))

def Admits (n m : Nat) : Prop :=
  ∃ r : Fin m → Fin m → Bool,
    IsTournament m r ∧
      ∀ s : Finset (Fin m), s.card = n →
        ∃ v : Fin m, v ∉ s ∧ ∀ u ∈ s, r v u = true

noncomputable def f (n : Nat) : Nat :=
  if h : ∃ m : Nat, Admits n m then Nat.find h else 0

theorem witness_pos : Admits 1 3 := by
  let r : Fin 3 → Fin 3 → Bool :=
    fun a b =>
      if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0)
      then true else false
  refine ⟨r, ?_, ?_⟩
  · constructor
    · intro a
      fin_cases a <;> simp [r]
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [r]
  · intro s hs
    obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp hs
    fin_cases u
    · refine ⟨(2 : Fin 3), ?_, ?_⟩
      · simp
      · intro u hu
        have hu' : u = (0 : Fin 3) := by simpa using hu
        subst u
        simp [r]
    · refine ⟨(0 : Fin 3), ?_, ?_⟩
      · simp
      · intro u hu
        have hu' : u = (1 : Fin 3) := by simpa using hu
        subst u
        simp [r]
    · refine ⟨(1 : Fin 3), ?_, ?_⟩
      · simp
      · intro u hu
        have hu' : u = (2 : Fin 3) := by simpa using hu
        subst u
        simp [r]

theorem witness_neg : ¬ Admits 1 2 := by
  intro h
  rcases h with ⟨r, ht, hp⟩
  have h0 := hp ({(0 : Fin 2)} : Finset (Fin 2)) (by simp)
  rcases h0 with ⟨v, hv, hrv⟩
  have hv1 : v = (1 : Fin 2) := by
    fin_cases v
    · simp at hv
    · rfl
  have h10 : r (1 : Fin 2) 0 = true := by
    have hh := hrv (0 : Fin 2) (by simp)
    simpa [hv1] using hh
  have h1 := hp ({(1 : Fin 2)} : Finset (Fin 2)) (by simp)
  rcases h1 with ⟨v, hv, hrv⟩
  have hv0 : v = (0 : Fin 2) := by
    fin_cases v
    · rfl
    · simp at hv
  have h01 : r (0 : Fin 2) 1 = true := by
    have hh := hrv (1 : Fin 2) (by simp)
    simpa [hv0] using hh
  have hc := (ht.2 (0 : Fin 2) 1 (by decide)).mp h01
  simp [h10] at hc

-- The source records problem 902 and the bibliographic identifiers Er63c,
-- Er82e, and SzSz65; the numerical conclusions 3, 7, and 19 are included
-- in the theorem below.

theorem erdos_902 :
    (f 1 = 3 ∧ f 2 = 7 ∧ f 3 = 19) ∧
      (∀ n : Nat, 2 ^ (n + 1) - 1 ≤ f n) ∧
      (∃ C N : Nat, ∀ n : Nat, N ≤ n →
        f n ≤ C * n ^ 2 * 2 ^ n) := by
  sorry

end