import Mathlib


noncomputable section
open scoped BigOperators
/-
We represent the interval {1, ..., N} by `Fin N`; translating by one
does not affect arithmetic progressions.  Since a coloring of N points
uses at most N colors, it suffices to use colors in `Fin N`.
-/
def IsCanonical (k N : Nat) : Prop :=
  ∀ c : Fin N → Fin N,
    ∃ a : Fin N, ∃ d : Fin (N + 1), ∃ f : Fin k → Fin N,
      d.val > 0 ∧
        (∀ i : Fin k, (f i).val = a.val + i.val * d.val) ∧
        ((∀ i j : Fin k, c (f i) = c (f j)) ∨
          (∀ i j : Fin k, i ≠ j → c (f i) ≠ c (f j)))

/-- `N` is the least integer having the required canonical Ramsey property. -/
def IsH (k N : Nat) : Prop :=
  IsCanonical k N ∧ ∀ M : Nat, M < N → ¬ IsCanonical k M

theorem witness_pos : IsCanonical 1 1 := by
  intro c
  refine ⟨0, 1, (fun _ => 0), ?_, ?_, ?_⟩
  · norm_num
  · intro i
    fin_cases i
    norm_num
  · left
    intro i j
    rfl

theorem witness_neg : ¬ IsCanonical 2 1 := by
  intro h
  have h' := h (fun _ => (0 : Fin 1))
  obtain ⟨a, d, f, hd, hf, hrest⟩ := h'
  have he := hf (1 : Fin 2)
  omega

/-
The conjectural estimate is expressed in an integer form of
H(k)^(1/k) / k → ∞: for every constant C, eventually
H(k) ≥ (C k)^k.
-/
theorem erdos_190 :
    (∀ k : Nat, ∃ N : Nat, IsH k N) ∧
      (∀ C : Nat,
        ∃ K : Nat,
          ∀ k : Nat, K ≤ k →
            ∀ N : Nat, IsH k N → (C * k) ^ k ≤ N) := by
  sorry

end