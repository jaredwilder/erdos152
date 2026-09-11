import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def Monotone3APFin {n : Nat} (p : Fin n → Fin n)
    (i j k : Fin n) : Prop :=
  ∃ (_ : Fin 3),
    i < j ∧ j < k ∧
      (((p i).val < (p j).val ∧ (p j).val < (p k).val) ∨
        ((p k).val < (p j).val ∧ (p j).val < (p i).val)) ∧
      (p i).val + (p k).val = 2 * (p j).val

def AvoidsMonotone3APFin {n : Nat} (c : Fin n → Bool) (b : Bool)
    (p : Equiv (Fin n) (Fin n)) : Prop :=
  ∀ i j k : Fin n,
    c (p i) = b →
      c (p j) = b →
        c (p k) = b →
          ¬ Monotone3APFin p i j k

def FiniteTwoColorAvoidance (n : Nat) : Prop :=
  (∃ x : Fin n, True) →
    ∃ c : Fin n → Bool,
      (∃ x : Fin n, c x = false) ∧
        (∃ x : Fin n, c x = true) ∧
          (∃ p₀ : Equiv (Fin n) (Fin n), AvoidsMonotone3APFin c false p₀) ∧
            (∃ p₁ : Equiv (Fin n) (Fin n), AvoidsMonotone3APFin c true p₁)

theorem witness_pos : FiniteTwoColorAvoidance 2 := by
  unfold FiniteTwoColorAvoidance
  intro _
  have no3 : ∀ i j k : Fin 2,
      ¬ Monotone3APFin (Equiv.refl (Fin 2)) i j k := by
    intro i j k h
    rcases h with ⟨_, hij, hjk, _⟩
    omega
  refine ⟨(fun x => if x = 0 then false else true), ?_, ?_, ?_, ?_⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by norm_num⟩
  · refine ⟨Equiv.refl _, ?_⟩
    intro i j k _ _ _
    exact no3 i j k
  · refine ⟨Equiv.refl _, ?_⟩
    intro i j k _ _ _
    exact no3 i j k

theorem witness_neg : ¬ FiniteTwoColorAvoidance 1 := by
  unfold FiniteTwoColorAvoidance
  intro h
  rcases h ⟨0, trivial⟩ with ⟨c, ⟨x, hx⟩, ⟨y, hy⟩, _, _⟩
  have hxy : x = y := Fin.ext (by omega)
  subst y
  rw [hx] at hy
  cases hy

def Monotone3APOn (s : Set ℕ) (p : Equiv s s) (i j k : s) : Prop :=
  ∃ (_ : Fin 3),
    i < j ∧ j < k ∧
      (((p i : ℕ) < (p j : ℕ) ∧ (p j : ℕ) < (p k : ℕ)) ∨
        ((p k : ℕ) < (p j : ℕ) ∧ (p j : ℕ) < (p i : ℕ))) ∧
      (p i : ℕ) + (p k : ℕ) = 2 * (p j : ℕ)

def PermutableAvoidsMonotone3AP (s : Set ℕ) : Prop :=
  ∃ p : Equiv s s, ∀ i j k : s, ¬ Monotone3APOn s p i j k

def ErdosProblem197 : Prop :=
  ∃ A B : Set ℕ,
    Disjoint A B ∧
      A ∪ B = Set.univ ∧
        PermutableAvoidsMonotone3AP A ∧
          PermutableAvoidsMonotone3AP B

theorem erdos_197 : ErdosProblem197 := by
  sorry

end