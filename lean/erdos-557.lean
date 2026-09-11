import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős Problem #557.

Let `RamseyProperty k n m T` mean that every symmetric `k`-colouring
of the edges of the complete graph on `Fin m` contains a monochromatic
copy of the graph `T` on `Fin n`.

The source metadata includes: #557, [ErGr75,p.516], problem #548,
problem #26, and the dates 08 February 2026 and 2026-08-30.
The extremal example is `S_n = K_{1,n-1}`, with the lower bound
`R_k(S_n) ≥ kn-O(k)`.
-/

def SymmetricColouring (k m : ℕ) (c : Fin m → Fin m → Fin k) : Prop :=
  ∀ u v, c u v = c v u

def RamseyProperty (k n m : ℕ) (T : SimpleGraph (Fin n)) : Prop :=
  ∀ c : Fin m → Fin m → Fin k,
    SymmetricColouring k m c →
      ∃ f : Fin n → Fin m,
        Function.Injective f ∧
          ∃ colour : Fin k,
            ∀ u v, T.Adj u v → c (f u) (f v) = colour

def RamseyTreeBound : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ C : ℕ, ∀ n : ℕ, ∀ T : SimpleGraph (Fin n),
      T.IsTree → RamseyProperty k n (k * n + C) T

theorem witness_pos :
    RamseyProperty 1 1 1 (⊥ : SimpleGraph (Fin 1)) := by
  intro c hc
  refine ⟨fun x => x, ?_, 0, ?_⟩
  · intro a b h
    exact h
  · intro u v huv
    exfalso
    simpa using huv

theorem witness_neg :
    ¬ RamseyProperty 1 2 1 (⊤ : SimpleGraph (Fin 2)) := by
  intro h
  let c : Fin 1 → Fin 1 → Fin 1 := fun _ _ => 0
  have hc : SymmetricColouring 1 1 c := by
    intro u v
    rfl
  obtain ⟨f, hf, colour, hmono⟩ := h c hc
  have hfi : f (0 : Fin 2) = f (1 : Fin 2) := Subsingleton.elim _ _
  have h01 : (0 : Fin 2) = 1 := hf hfi
  have hval := congrArg Fin.val h01
  norm_num at hval

theorem erdos_problem_557 : RamseyTreeBound := by
  sorry

end