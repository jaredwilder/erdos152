import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped BigOperators
open Filter

/-- A finite `t`-uniform hypergraph on the vertex set `Fin n`. -/
abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

def IsUniform (n t : ℕ) (H : Hypergraph n) : Prop :=
  ∀ e ∈ H, e.card = t

/-- The hypergraph contains a copy of the complete `t`-partite
`t`-uniform hypergraph with `r` vertices in each class. -/
def ContainsCompletePartite (n t r : ℕ) (H : Hypergraph n) : Prop :=
  ∃ parts : Fin t → Finset (Fin n),
    (∀ i, (parts i).card = r) ∧
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    (∀ f : Fin t → Fin n,
      (∀ i, f i ∈ parts i) →
        (Finset.univ.image f : Finset (Fin n)) ∈ H)

def KFree (n t r : ℕ) (H : Hypergraph n) : Prop :=
  IsUniform n t H ∧ ¬ ContainsCompletePartite n t r H

def allHypergraphs (n : ℕ) : Finset (Hypergraph n) :=
  (Finset.univ : Finset (Finset (Fin n))).powerset

/-- The finite Turán number obtained by maximizing over all hypergraphs
on `Fin n`. -/
def turanNumber (n t r : ℕ) : ℕ :=
  ((allHypergraphs n).filter (fun H => decide (KFree n t r H))).sup Finset.card

/-- The usual `o(1)` lower-bound assertion, expressed with an epsilon
formulation of asymptotic comparison. -/
def AsymptoticLowerBound (t r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      (turanNumber n t r : ℝ) ≥
        Real.rpow (n : ℝ)
          ((t : ℝ) - Real.rpow (r : ℝ) (1 - (t : ℝ)) - ε)

/-- Erdős problem 1158: the proposed lower bound for all positive `t,r`. -/
theorem erdos_problem_1158 :
    ∀ t r : ℕ, 0 < t → 0 < r → AsymptoticLowerBound t r := by
  sorry

def sourceProblemNumber : ℕ := 1158

def sourceLowerBoundCaseTwo : ℕ := 2

def sourceKnownCaseThree : ℕ := 3

theorem witness_pos :
    KFree 1 1 1 (∅ : Hypergraph 1) := by
  refine ⟨?_, ?_⟩
  · simp [IsUniform]
  · intro h
    rcases h with ⟨parts, hcard, hdisjoint, hmem⟩
    have hnonempty : (parts 0).Nonempty := by
      apply Finset.card_pos.mp
      simpa [hcard 0]
    have hp : (0 : Fin 1) ∈ parts 0 := by
      rcases hnonempty with ⟨x, hx⟩
      simpa [Fin.eq_zero x] using hx
    have hall : ∀ i : Fin 1, (0 : Fin 1) ∈ parts i := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      simpa [hi] using hp
    have hbad := hmem (fun _ : Fin 1 => (0 : Fin 1)) hall
    simpa using hbad

def singletonEdgeHypergraph : Hypergraph 1 :=
  {Finset.univ}

theorem witness_neg :
    ¬ KFree 1 1 1 singletonEdgeHypergraph := by
  intro h
  apply h.2
  refine ⟨fun _ : Fin 1 => Finset.univ, ?_, ?_, ?_⟩
  · intro i
    simp
  · intro i j hij
    have hij' : i = j :=
      (Fin.eq_zero i).trans (Fin.eq_zero j).symm
    exact (hij hij').elim
  · intro f hf
    have hf_eq : f = (fun _ : Fin 1 => (0 : Fin 1)) := by
      funext i
      exact Fin.eq_zero (f i)
    have himg :
        (Finset.univ.image f : Finset (Fin 1)) = Finset.univ := by
      rw [hf_eq]
      ext x
      simp [Fin.eq_zero x]
    rw [himg]
    simp [singletonEdgeHypergraph]

end