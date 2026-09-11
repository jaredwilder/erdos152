import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def edgeColor {n : ℕ} (c : Fin n → Fin n → Bool)
    (i j : Fin n) : Bool :=
  if i < j then c i j else c j i

def Monochromatic {k n : ℕ} (c : Fin n → Fin n → Bool)
    (f : Fin k → Fin n) (colour : Bool) : Prop :=
  ∀ a b : Fin k, a < b → edgeColor c (f a) (f b) = colour

def Ramsey (k n : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Bool,
    ∃ f : Fin k → Fin n,
      Function.Injective f ∧
        (Monochromatic c f true ∨ Monochromatic c f false)

noncomputable def RamseyNumber (k : ℕ) : ℕ :=
  if h : ∃ n : ℕ, Ramsey k n then
    Nat.find h
  else
    0

theorem witness_pos : Ramsey 1 1 := by
  intro c
  let f : Fin 1 → Fin 1 := fun _ => 0
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    exact Subsingleton.elim _ _
  · left
    intro a b hab
    have hEq : a = b := Subsingleton.elim _ _
    subst b
    exact (lt_irrefl _ hab).elim

theorem witness_neg : ¬ Ramsey 2 1 := by
  intro h
  obtain ⟨f, hf, hmono⟩ := h (fun _ _ => false)
  have h01 : (0 : Fin 2) = 1 := hf (Subsingleton.elim _ _)
  have hv : (0 : ℕ) = 1 := congrArg Fin.val h01
  norm_num at hv

theorem erdos_problem_1029 :
    Filter.Tendsto
      (fun k : ℕ =>
        (RamseyNumber k : ℝ) /
          ((k : ℝ) * Real.rpow (2 : ℝ) ((k : ℝ) / 2)))
      Filter.atTop Filter.atTop := by
  sorry

end