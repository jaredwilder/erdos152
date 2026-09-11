import Mathlib


noncomputable section
open scoped BigOperators
open scoped BigOperators

/-
  The finite encoding below uses at most k optional summands.  An exponent is
  bounded by n: in any representation of n, every nonnegative summand is
  at most n, so this bound does not change the represented numbers.
-/

def Represents (n k : Nat) : Prop :=
  ∃ p : Fin (n + 1),
    ∃ choices : Fin k → Option (Fin (n + 1)),
      Nat.Prime p.val ∧
        n =
          p.val +
            ∑ i : Fin k,
              match choices i with
              | none => 0
              | some e => 2 ^ e.val

/-- The Erdős problem asks whether some fixed number of powers suffices
for every integer beyond a fixed threshold. -/
def ErdosProblem10 : Prop :=
  ∃ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n → Represents n k

def sourceNumerals : List Nat :=
  [10, 77, 80, 96, 28, 85, 92, 95, 97, 75, 98, 3, 4, 1117175146, 2, 9, 11,
    16, 0, 1, 2026, 4, 11, 8, 30, 387053]

theorem witness_pos : Represents 2 0 := by
  unfold Represents
  refine ⟨⟨2, by omega⟩, (fun i : Fin 0 => Fin.elim0 i), Nat.prime_two, ?_⟩
  simp

theorem witness_neg : ¬ Represents 1 0 := by
  unfold Represents
  intro h
  rcases h with ⟨p, choices, hp, hEq⟩
  simp at hEq
  have hval : p.val = 1 := by
    omega
  have hp1 : Nat.Prime 1 := by
    rw [← hval]
    exact hp
  exact (by norm_num : ¬ Nat.Prime 1) hp1

theorem erdos_problem_10 : ErdosProblem10 := by
  sorry

end