import Mathlib

noncomputable section
open scoped BigOperators
open scoped Classical
/-
Erdős problem 1171.

The original statement concerns the infinite partition relation
ω₁^2 → (ω₁ω, 3, ..., 3)_{k+1}^2.
This file records its decidable finite shadow: a finite complete graph is
colored with k+1 colors, and either color 0 contains a clique of prescribed
size m, or one of the remaining colors contains a triangle.
The parameters n and m range over finite approximations to the two infinite
cardinal expressions in the original question.
-/

def edgeColor {n k : ℕ}
    (f : Fin n → Fin n → Fin (k + 1))
    (i j : Fin n) : Fin (k + 1) :=
  if i.val < j.val then f i j else f j i

def monoClique {n k : ℕ}
    (f : Fin n → Fin n → Fin (k + 1))
    (c : Fin (k + 1))
    (r : ℕ) : Prop :=
  ∃ s : Finset (Fin n),
    s.card = r ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → edgeColor f i j = c

def finiteArrow (n k m : ℕ) : Prop :=
  ∀ f : Fin n → Fin n → Fin (k + 1),
    monoClique f 0 m ∨
      ∃ c : Fin (k + 1), c ≠ 0 ∧ monoClique f c 3

theorem witness_pos : finiteArrow 1 1 1 := by
  intro f
  left
  refine ⟨({0} : Finset (Fin 1)), by simp, ?_⟩
  intro i hi j hj hne
  have hi' : i = (0 : Fin 1) := by simpa using hi
  have hj' : j = (0 : Fin 1) := by simpa using hj
  exact (hne (hi'.trans hj'.symm)).elim

theorem witness_neg : ¬ finiteArrow 2 1 3 := by
  intro h
  let f : Fin 2 → Fin 2 → Fin (1 + 1) := fun _ _ => 0
  rcases h f with h0 | ⟨c, hc, h1⟩
  · rcases h0 with ⟨s, hs, hmem⟩
    have hcard : s.card ≤ 2 := by
      simpa using (Finset.card_le_univ s)
    omega
  · rcases h1 with ⟨s, hs, hmem⟩
    have hcard : s.card ≤ 2 := by
      simpa using (Finset.card_le_univ s)
    omega

/-
Finite decidable formulation of the question.  The literal 3 is the
triangle size appearing in the source, while k + 1 is its number of colors.
-/
theorem erdos_1171 :
    ∀ k : ℕ, ∀ m : ℕ, ∃ n : ℕ, finiteArrow n k m := by
  sorry

end