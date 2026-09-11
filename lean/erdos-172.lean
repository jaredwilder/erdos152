import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
Erdős problem #172 asks whether every finite colouring of ℕ admits
arbitrarily large finite sets whose sums and products of distinct elements
all have one colour.  The source also records the 3-term configuration
{x, x + y, x * y}, the 7-colour infinite-set obstruction, and the
references [Er77c], [ErGr79], [ErGr80], [Hi80], [1198], [Mo17], [Al23],
and [BoSa22].  The source metadata includes 172, 7, 2, 1198, 17, 23, 0,
22, 06, 2026, and 08-30.
-/

/-- The positive natural number represented by an element of `Fin B`. -/
def positiveValue {B : ℕ} (x : Fin B) : ℕ :=
  x.val + 1

/--
A finite set has the required monochromatic sum-and-product property for a
colouring `c` if there is one colour shared by every sum and product of two
distinct members.
-/
def Good
    {k B : ℕ} (c : ℕ → Fin (k + 1)) (A : Finset (Fin B)) : Prop :=
  ∃ q : Fin (k + 1),
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      c (positiveValue x + positiveValue y) = q ∧
        c (positiveValue x * positiveValue y) = q

/--
`Pattern c B r` is the bounded, decidable approximation asserting that
there is a set of at least `r` positive natural numbers below `B` with the
required property.
-/
def Pattern
    {k : ℕ} (c : ℕ → Fin (k + 1)) (B r : ℕ) : Prop :=
  ∃ A : Finset (Fin B), A.card ≥ r ∧ Good c A

theorem witness_pos :
    Pattern (fun _ : ℕ => (0 : Fin 1)) 1 1 := by
  refine ⟨({0} : Finset (Fin 1)), by simp, ?_⟩
  refine ⟨(0 : Fin 1), ?_⟩
  intro x hx y hy hxy
  have hx0 : x = (0 : Fin 1) := by
    simpa using hx
  have hy0 : y = (0 : Fin 1) := by
    simpa using hy
  exfalso
  apply hxy
  rw [hx0, hy0]

theorem witness_neg :
    ¬ Pattern (fun _ : ℕ => (0 : Fin 1)) 1 2 := by
  intro h
  rcases h with ⟨A, hcard, _⟩
  have hle : A.card ≤ 1 := by
    calc
      A.card ≤ (Finset.univ : Finset (Fin 1)).card :=
        Finset.card_le_card (Finset.subset_univ A)
      _ = 1 := by simp
  omega

/--
Formalization of Erdős problem #172: every finite colouring admits
arbitrarily large finite monochromatic sum-and-product configurations.
-/
theorem erdos_172 :
    ∀ (k : ℕ) (c : ℕ → Fin (k + 1)) (r : ℕ),
      ∃ B : ℕ, Pattern c B r := by
  sorry

end