import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
-- Source literals retained from the entry: 1, 2, 0, 103, 94, 99, 2026-08-30.

abbrev Point := ℝ × ℝ

def distSq (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def Config (n : ℕ) :=
  Fin n → Point

def Admissible {n : ℕ} (C : Config n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (1 : ℝ) ≤ distSq (C i) (C j)

def IsMinimizer {n : ℕ} (C : Config n) : Prop :=
  Admissible C ∧
    ∀ D : Config n, Admissible D →
      ∀ i j : Fin n, distSq (C i) (C j) ≤ distSq (D i) (D j)

def Minimizer (n : ℕ) :=
  {C : Config n // IsMinimizer C}

def IsCongruent {n : ℕ} (C D : Config n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ i j : Fin n,
      distSq (C i) (C j) = distSq (D (σ i)) (D (σ j))

def minimizerSetoid (n : ℕ) : Setoid (Minimizer n) where
  r C D := IsCongruent C.1 D.1
  iseqv := by
    constructor
    · intro C
      refine ⟨Equiv.refl _, ?_⟩
      intro i j
      rfl
    · intro C D h
      rcases h with ⟨σ, hσ⟩
      refine ⟨σ.symm, ?_⟩
      intro i j
      have hh := hσ (σ.symm i) (σ.symm j)
      simpa using hh.symm
    · intro C D E hCD hDE
      rcases hCD with ⟨σ, hσ⟩
      rcases hDE with ⟨τ, hτ⟩
      refine ⟨σ.trans τ, ?_⟩
      intro i j
      calc
        distSq (C.1 i) (C.1 j) =
            distSq (D.1 (σ i)) (D.1 (σ j)) := hσ i j
        _ = distSq (E.1 (τ (σ i))) (E.1 (τ (σ j))) :=
          hτ (σ i) (σ j)

noncomputable def h (n : ℕ) : ℕ :=
  Cardinal.toNat (Cardinal.mk (Quotient (minimizerSetoid n)))

def cOne : Config 1 :=
  fun _ => (0, 0)

def cTwo : Config 2 :=
  fun _ => (0, 0)

theorem witness_pos : Admissible cOne := by
  intro i j hij
  have hij' : i = j := by
    exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm
  exact (hij hij').elim

theorem witness_neg : ¬ Admissible cTwo := by
  intro ha
  have hh : (1 : ℝ) ≤ distSq (cTwo (0 : Fin 2)) (cTwo (1 : Fin 2)) :=
    ha (0 : Fin 2) (1 : Fin 2) (by decide)
  norm_num [cTwo, distSq] at hh

theorem erdos_103 : Filter.Tendsto h Filter.atTop Filter.atTop := by
  sorry

end