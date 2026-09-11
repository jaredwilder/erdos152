import Mathlib

noncomputable section
open scoped BigOperators
open scoped Classical

namespace Fix

def Graph (n : ℕ) := Fin n → Fin n → Bool

def IsGraph {n : ℕ} (G : Graph n) : Prop :=
  (∀ v, G v v = false) ∧ ∀ v w, G v w = G w v

def NoIsolated {n : ℕ} (G : Graph n) : Prop :=
  ∀ v, ∃ w, G v w = true

def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G p.1 p.2 = true)).card

def ContainsCycle (k N : ℕ) (G : Graph N) : Prop :=
  ∃ f : Fin (2 * k + 1) → Fin N,
    Function.Injective f ∧
      ∀ i : Fin (2 * k + 1),
        G (f i)
          (f ⟨(i.val + 1) % (2 * k + 1), by
            exact Nat.mod_lt _ (by omega)⟩) = true

def EmbedsInComplement {n N : ℕ} (H : Graph n) (G : Graph N) : Prop :=
  ∃ f : Fin n → Fin N,
    Function.Injective f ∧
      ∀ ⦃v w : Fin n⦄, H v w = true → G (f v) (f w) ≠ true

def RamseyAt (k : ℕ) (c : ℚ) {n : ℕ} (H : Graph n) : Prop :=
  IsGraph H →
    NoIsolated H →
      ∀ G : Graph (Nat.floor (c * (edgeCount H : ℚ))),
        IsGraph G →
          ContainsCycle k _ G ∨ EmbedsInComplement H G

def Valid (k : ℕ) (c : ℚ) : Prop :=
  1 ≤ k ∧ ∀ n : ℕ, ∀ H : Graph n, RamseyAt k c H

def emptyGraph (n : ℕ) : Graph n :=
  fun _ _ => false

def oneEdgeGraph : Graph 2 :=
  fun v w => decide (v ≠ w)

theorem witness_pos :
    RamseyAt 1 1 (emptyGraph 0) := by
  unfold RamseyAt
  intro _ _
  intro G _
  right
  refine ⟨fun v => Fin.elim0 v, ?_, ?_⟩
  · intro v
    exact Fin.elim0 v
  · intro v
    exact Fin.elim0 v

theorem witness_neg :
    ¬ RamseyAt 1 1 oneEdgeGraph := by
  intro hr
  have hI : IsGraph oneEdgeGraph := by
    constructor
    · intro v
      fin_cases v <;> rfl
    · intro v w
      fin_cases v <;> fin_cases w <;> rfl
  have hN : NoIsolated oneEdgeGraph := by
    intro v
    fin_cases v
    · exact ⟨⟨1, by omega⟩, by rfl⟩
    · exact ⟨⟨0, by omega⟩, by rfl⟩
  have hed : edgeCount oneEdgeGraph = 1 := by
    native_decide
  have heq : Nat.floor (1 * (edgeCount oneEdgeGraph : ℚ)) = 1 := by
    norm_num [hed]
  unfold RamseyAt at hr
  rw [heq] at hr
  have hG : IsGraph (emptyGraph 1) := by
    constructor
    · intro v
      rfl
    · intro v w
      rfl
  have h := hr hI hN (emptyGraph 1) hG
  rcases h with hc | he
  · rcases hc with ⟨f, hf, _⟩
    let i : Fin (2 * 1 + 1) := ⟨0, by omega⟩
    let j : Fin (2 * 1 + 1) := ⟨1, by omega⟩
    have hij : i = j := hf (Subsingleton.elim _ _)
    have hv := congrArg Fin.val hij
    dsimp [i, j] at hv
    omega
  · rcases he with ⟨f, hf, _⟩
    let i : Fin 2 := ⟨0, by omega⟩
    let j : Fin 2 := ⟨1, by omega⟩
    have hij : i = j := hf (Subsingleton.elim _ _)
    have hv := congrArg Fin.val hij
    dsimp [i, j] at hv
    omega

theorem main_conjecture :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c : ℚ, IsLeast {q : ℚ | Valid k q} c := by
  sorry

end Fix

end