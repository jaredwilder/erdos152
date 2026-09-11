import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
A 3-uniform hypergraph is represented by a vertex type together with a
symmetric irreflexive ternary edge relation.
-/
def IsThreeUniform (n : ℕ) (e : Fin n → Fin n → Fin n → Bool) : Prop :=
  (∀ a b c, e a b c = true → a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
  (∀ a b c, e a b c = e b a c) ∧
  (∀ a b c, e a b c = e a c b)

structure FiniteThreeHypergraph where
  n : ℕ
  edge : Fin n → Fin n → Fin n → Bool
  uniform : IsThreeUniform n edge

structure ThreeUniformHypergraph (V : Type) where
  edge : V → V → V → Prop
  distinct :
    ∀ ⦃a b c : V⦄, edge a b c → a ≠ b ∧ a ≠ c ∧ b ≠ c
  swap12 : ∀ a b c, edge a b c ↔ edge b a c
  swap23 : ∀ a b c, edge a b c ↔ edge a c b

def ProperColoring {V : Type} (H : ThreeUniformHypergraph V)
    (f : V → ℕ) : Prop :=
  ∀ ⦃a b c : V⦄, H.edge a b c →
    f a ≠ f b ∨ f a ≠ f c ∨ f b ≠ f c

/-- A hypergraph has chromatic number at most ℵ₀ exactly when it has a
coloring by the natural numbers. -/
def CountablyColorable {V : Type} (H : ThreeUniformHypergraph V) : Prop :=
  ∃ f : V → ℕ, ProperColoring H f

def Embeds (P : FiniteThreeHypergraph) {V : Type}
    (H : ThreeUniformHypergraph V) : Prop :=
  ∃ f : Fin P.n → V,
    Function.Injective f ∧
      ∀ ⦃a b c : Fin P.n⦄, P.edge a b c = true →
        H.edge (f a) (f b) (f c)

/-- The finite 3-uniform hypergraphs which occur in every
3-uniform hypergraph of chromatic number greater than ℵ₀. -/
def AppearsInEveryUncountablyChromaticHypergraph
    (P : FiniteThreeHypergraph) : Prop :=
  ∀ (V : Type) (H : ThreeUniformHypergraph V),
    ¬ CountablyColorable H → Embeds P H

theorem witness_pos :
    IsThreeUniform 0 (fun _ _ _ => false) := by
  simp [IsThreeUniform]

theorem witness_neg :
    ¬ IsThreeUniform 3
      (fun a b c => if a = 0 ∧ b = 0 ∧ c = 0 then true else false) := by
  intro h
  have h' := h.1 (0 : Fin 3) 0 0 (by simp)
  exact h'.1 rfl

theorem erdos_problem_593 :
    ∀ P : FiniteThreeHypergraph,
      AppearsInEveryUncountablyChromaticHypergraph P := by
  sorry

end