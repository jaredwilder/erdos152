import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
abbrev FiniteGraph (N : ℕ) := Finset (Finset (Fin N))

def graphAdj {N : ℕ} (G : FiniteGraph N) (u v : Fin N) : Prop :=
  ({u, v} : Finset (Fin N)) ∈ G

def containsC4 {N : ℕ} (G : FiniteGraph N) : Prop :=
  ∃ f : Fin 4 → Fin N,
    Function.Injective f ∧
      graphAdj G (f 0) (f 1) ∧
      graphAdj G (f 1) (f 2) ∧
      graphAdj G (f 2) (f 3) ∧
      graphAdj G (f 3) (f 0)

def containsClique {N n : ℕ} (G : FiniteGraph N) : Prop :=
  ∃ f : Fin n → Fin N,
    Function.Injective f ∧
      ∀ i j : Fin n, i ≠ j → graphAdj G (f i) (f j)

def ramseyProperty (N n : ℕ) : Prop :=
  ∀ G : FiniteGraph N, ¬ containsC4 G → containsClique (n := n) G

noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {N : ℕ | ramseyProperty N n}

theorem witness_pos : ramseyProperty 1 1 := by
  intro G _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i j h
    exact Subsingleton.elim _ _
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

theorem witness_neg : ¬ ramseyProperty 1 2 := by
  intro hp
  have hno : ¬ containsC4 (∅ : FiniteGraph 1) := by
    rintro ⟨f, hf, _⟩
    have h01 : (0 : Fin 4) ≠ 1 := by decide
    have hEq : f (0 : Fin 4) = f 1 := Subsingleton.elim _ _
    exact h01 (hf hEq)
  rcases hp (∅ : FiniteGraph 1) hno with ⟨f, hf, _⟩
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hEq : f (0 : Fin 2) = f 1 := Subsingleton.elim _ _
  exact h01 (hf hEq)

theorem erdos_problem_159 :
    ∃ c : ℝ, 0 < c ∧
      ∃ K : ℝ, 0 < K ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (ramseyNumber n : ℝ) ≤ K * Real.rpow (n : ℝ) (2 - c) := by
  sorry

end