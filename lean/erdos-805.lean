import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
-- Erdos problem 805, attributed in the source to [Er91], with the
-- subsequent references [AlSu07], [ABS21].  The source also records the
-- bounds involving 2, 3, and the exponent 1/2.
--
-- We use the base-2 natural logarithm as a decidable finite analogue of log.
def logN (n : ℕ) : ℕ := Nat.log 2 n

def IsClique {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ ⦃u : Fin n⦄, u ∈ S →
    ∀ ⦃v : Fin n⦄, v ∈ S → u ≠ v → adj u v = true

def IsIndependent {n : ℕ} (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ ⦃u : Fin n⦄, u ∈ S →
    ∀ ⦃v : Fin n⦄, v ∈ S → u ≠ v → adj u v = false

def IsSimpleGraph {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  (∀ v, adj v v = false) ∧
    (∀ u v, adj u v = adj v u)

def HasRequiredGraph (g : ℕ → ℕ) (n : ℕ) : Prop :=
  n > g n ∧
    logN n ^ 2 ≤ g n ∧
    ∃ adj : Fin n → Fin n → Bool,
      IsSimpleGraph adj ∧
        ∀ S : Finset (Fin n), S.card = g n →
          (∃ T : Finset (Fin n),
            T ⊆ S ∧ logN n ≤ T.card ∧ IsClique adj T) ∧
          (∃ T : Finset (Fin n),
            T ⊆ S ∧ logN n ≤ T.card ∧ IsIndependent adj T)

-- The concrete positive witness is the vacuous zero-sized induced-subgraph
-- case at n = 1.
theorem witness_pos :
    HasRequiredGraph (fun _ : ℕ => 0) 1 := by
  refine ⟨by norm_num, by norm_num [logN], ?_⟩
  let adj : Fin 1 → Fin 1 → Bool := fun _ _ => false
  refine ⟨adj, ?_, ?_⟩
  · constructor
    · intro v
      rfl
    · intro u v
      rfl
  · intro S hS
    have hS' : S.card = 0 := by
      simpa using hS
    have hEmpty : S = ∅ := Finset.card_eq_zero.mp hS'
    subst S
    constructor
    · refine ⟨∅, by simp, ?_, ?_⟩
      · norm_num [logN]
      · simp [IsClique]
    · refine ⟨∅, by simp, ?_, ?_⟩
      · norm_num [logN]
      · simp [IsIndependent]

-- At n = 2, the lower bound log(n)^2 ≤ g(n) already fails for g(n) = 0.
theorem witness_neg :
    ¬ HasRequiredGraph (fun _ : ℕ => 0) 2 := by
  intro h
  rcases h with ⟨_, hbound, _⟩
  norm_num [logN] at hbound

def CubeQuestion : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    HasRequiredGraph (fun m : ℕ => logN m ^ 3) n

theorem erdos_805_cube_question : CubeQuestion := by
  sorry

end