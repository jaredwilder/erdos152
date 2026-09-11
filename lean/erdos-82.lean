import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  A graph on `Fin n` is represented by its Boolean adjacency matrix.  The
  predicate below imposes the usual loop-free and symmetric conditions.
-/

def IsGraph (n : ℕ) (a : Fin n → Fin n → Bool) : Prop :=
  (∀ v, a v v = false) ∧ ∀ u v, a u v = a v u

def BoolGraph (n : ℕ) := {a : Fin n → Fin n → Bool // IsGraph n a}

def inducedDegree {n : ℕ} (g : BoolGraph n) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter (fun w => g.1 v w = true)).card

def IsRegularInduced {n : ℕ} (g : BoolGraph n) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, inducedDegree g S u = inducedDegree g S v

def HasRegularAtLeast (n k : ℕ) (g : BoolGraph n) : Prop :=
  ∃ S : Finset (Fin n), k ≤ S.card ∧ IsRegularInduced g S

def UniversalRegular (n k : ℕ) : Prop :=
  ∀ g : BoolGraph n, HasRegularAtLeast n k g

def F (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => UniversalRegular n k) n

/-
  The source also records the numerical facts F(5)=3 and F(7)=4, the
  Ramsey-theoretic logarithmic lower bound, and the later bounds involving
  1, 2, 3, 4, 5, 6, 7, 9, 12, 17, 21, 29, 30, 163, and 1031.
  The original item is Erdos problem 82, with references Er93, Er95,
  Er97d, AKS07, DyMc26, and a page update dated 10 April 2026.
-/

/-- Every graph on one vertex has a regular induced subgraph of size at least 1. -/
theorem witness_pos : UniversalRegular 1 1 := by
  intro g
  refine ⟨Finset.univ, by simp, ?_⟩
  intro u hu v hv
  have huv : u = v := Subsingleton.elim _ _
  subst v
  rfl

/-- No graph on one vertex has a regular induced subgraph of size at least 2. -/
theorem witness_neg : ¬ UniversalRegular 1 2 := by
  intro h
  let g : BoolGraph 1 :=
    ⟨fun _ _ => false, by
      constructor <;> simp⟩
  have hg := h g
  rcases hg with ⟨S, hcard, hreg⟩
  have hle : S.card ≤ 1 := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  omega

/-- The conjecture that F(n) / log n tends to infinity. -/
theorem main_conjecture :
    ∀ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 < n →
      C ≤ (F n : ℝ) / Real.log (n : ℝ) := by
  sorry

end