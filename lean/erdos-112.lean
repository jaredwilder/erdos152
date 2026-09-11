import Mathlib


noncomputable section
open scoped BigOperators

namespace Problem112

/-!
Formalization of Erdős Problem 112.

The source mentions [ErRa67], [LaMi97], the bounds involving `2`, `3`, and `1`,
the special case `k(n,3) ≤ n^2`, the alternative directed-path value
`(n-1)(m-1)`, and the bound `3^(n+2*m)`.
-/

abbrev DirectedGraph (k : ℕ) := Fin k → Fin k → Bool

def InjectiveMap {a b : ℕ} (f : Fin a → Fin b) : Prop :=
  ∀ i j, f i = f j → i = j

def HasIndependentSet (n m k : ℕ) (g : DirectedGraph k) : Prop :=
  ∃ f : Fin n → Fin k,
    InjectiveMap f ∧
      ∀ i j, i ≠ j →
        g (f i) (f j) = false ∧ g (f j) (f i) = false

def HasTransitiveTournament (n m k : ℕ) (g : DirectedGraph k) : Prop :=
  ∃ f : Fin m → Fin k,
    InjectiveMap f ∧
      ∀ i j, i < j → g (f i) (f j) = true

def HasRequiredConfiguration (n m k : ℕ) (g : DirectedGraph k) : Prop :=
  HasIndependentSet n m k g ∨ HasTransitiveTournament n m k g

def Good (n m k : ℕ) : Prop :=
  ∀ g : DirectedGraph k, HasRequiredConfiguration n m k g

def Minimal (n m k : ℕ) : Prop :=
  Good n m k ∧ ∀ j, j < k → ¬ Good n m j

def ErdosBound (n m : ℕ) : ℕ :=
  (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3)

def QuadraticBound (n : ℕ) : ℕ :=
  n ^ 2

def RamseyStyleBound (n m : ℕ) : ℕ :=
  3 ^ (n + 2 * m)

theorem witness_pos : Good 1 1 1 := by
  intro g
  left
  refine ⟨fun _ => (0 : Fin 1), ?_, ?_⟩
  · intro i j h
    exact Subsingleton.elim _ _
  · intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim

theorem witness_neg : ¬ Good 2 2 1 := by
  intro h
  have hc := h (fun _ _ => false)
  rcases hc with hc | hc
  · rcases hc with ⟨f, hf, _⟩
    have heq : (0 : Fin 2) = 1 := hf 0 1 (Subsingleton.elim _ _)
    have hv := congrArg Fin.val heq
    omega
  · rcases hc with ⟨f, hf, _⟩
    have heq : (0 : Fin 2) = 1 := hf 0 1 (Subsingleton.elim _ _)
    have hv := congrArg Fin.val heq
    omega

theorem erdos_problem_112 :
    ∀ n m, 2 ≤ n → 2 ≤ m →
      ∃ k, Minimal n m k ∧
        k ≤ ErdosBound n m ∧
        (m = 3 → k ≤ QuadraticBound n) ∧
        k ≤ RamseyStyleBound n m := by
  sorry

end Problem112

end