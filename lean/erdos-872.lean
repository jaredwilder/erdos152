import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def Legal (n : ℕ) (s : Finset (Fin (n + 1))) (x : Fin (n + 1)) : Prop :=
  2 ≤ x.val ∧ ∀ y ∈ s, ¬ x.val ∣ y.val ∧ ¬ y.val ∣ x.val

def guaranteedFrom (n : ℕ) (s : Finset (Fin (n + 1))) (turn : Bool) : ℕ → Prop
  | 0 => True
  | k + 1 =>
      if turn = true then
        ∃ x : Fin (n + 1),
          Legal n s x ∧ guaranteedFrom n (insert x s) false k
      else
        (∃ x : Fin (n + 1), Legal n s x) ∧
          ∀ x : Fin (n + 1), Legal n s x →
            guaranteedFrom n (insert x s) true k

def Guaranteed (n k : ℕ) : Prop :=
  guaranteedFrom n (∅ : Finset (Fin (n + 1))) true k

def AtLeast (n k : ℕ) (q : ℚ) : Prop :=
  (k : ℚ) ≥ q * (n : ℚ)

def FirstClaim : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ k : ℕ, Guaranteed n k ∧ AtLeast n k ε

def SecondClaim : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ k : ℕ, Guaranteed n k ∧ AtLeast n k ((1 - ε) / 2)

def Question : Prop :=
  FirstClaim ∧ SecondClaim

theorem witness_pos : Guaranteed 3 1 := by
  change ∃ x : Fin (3 + 1), Legal 3 ∅ x ∧
    guaranteedFrom 3 (insert x ∅) false 0
  refine ⟨⟨2, by decide⟩, ?_, ?_⟩
  · norm_num [Legal]
  · simp [guaranteedFrom]

theorem witness_neg : ¬ Guaranteed 3 3 := by
  intro h
  change ∃ x : Fin (3 + 1), Legal 3 ∅ x ∧
    guaranteedFrom 3 (insert x ∅) false 2 at h
  rcases h with ⟨x, hx, h⟩
  change
    (∃ y : Fin (3 + 1), Legal 3 (insert x ∅) y) ∧
      ∀ y : Fin (3 + 1), Legal 3 (insert x ∅) y →
        guaranteedFrom 3 (insert y (insert x ∅)) true 1 at h
  rcases h with ⟨⟨y, hy⟩, hall⟩
  have hzgame := hall y hy
  change ∃ z : Fin (3 + 1), Legal 3 (insert y (insert x ∅)) z ∧
    guaranteedFrom 3 (insert z (insert y (insert x ∅))) false 0 at hzgame
  rcases hzgame with ⟨z, hz, _⟩
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Legal] at *

theorem erdos_872_question : Question := by
  sorry

end