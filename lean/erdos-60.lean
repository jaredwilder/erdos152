import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical

namespace ErdosProblem60

/-!
Erdős Problem #60 asks whether graphs on `n` vertices with more than
`ex(n; C₄)` edges contain a number of copies of `C₄` bounded below by
a constant multiple of `n^(1/2)`.

The numerical literals occurring in the source include: 60, 4, 90, 93, 335,
2, 765, 21, 2025, and 2026.
-/

structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Bool
deriving DecidableEq, Fintype

def emptyGraph (n : ℕ) : Graph n :=
  ⟨fun _ _ => false⟩

def edge {n : ℕ} (G : Graph n) (a b : Fin n) : Bool :=
  decide (a ≠ b) && (G.adj a b || G.adj b a)

def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  (Finset.univ.filter
    (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ edge G p.1 p.2 = true)).card

structure Quad (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
deriving DecidableEq, Fintype

def isC4 {n : ℕ} (G : Graph n) (q : Quad n) : Prop :=
  q.a < q.b ∧ q.b < q.c ∧ q.c < q.d ∧
    edge G q.a q.b = true ∧
    edge G q.b q.c = true ∧
    edge G q.c q.d = true ∧
    edge G q.d q.a = true

def c4Count {n : ℕ} (G : Graph n) : ℕ :=
  (Finset.univ.filter (fun q : Quad n => isC4 G q)).card

def ex (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun G : Graph n => c4Count G = 0)).sup edgeCount

def AboveEx {n : ℕ} (G : Graph n) : Prop :=
  edgeCount G > ex n

def C4Rich {n : ℕ} (G : Graph n) : Prop :=
  0 < c4Count G

def cycle4 : Graph 4 :=
  ⟨fun a b =>
    decide (
      (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
      (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
      (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
      (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3))⟩

theorem witness_pos : C4Rich cycle4 := by
  classical
  unfold C4Rich c4Count
  apply Finset.card_pos.mpr
  refine ⟨⟨0, 1, 2, 3⟩, ?_⟩
  simp [isC4, cycle4, edge]

theorem witness_neg : ¬ C4Rich (emptyGraph 4) := by
  classical
  unfold C4Rich c4Count
  have hfilter :
      (Finset.univ.filter (fun q : Quad 4 => isC4 (emptyGraph 4) q)) = ∅ := by
    ext q
    simp [isC4, emptyGraph, edge]
  rw [hfilter]
  simp

def ErdosConjecture : Prop :=
  ∃ d : ℕ, 0 < d ∧
    ∀ (n : ℕ) (G : Graph n),
      AboveEx G →
        d * c4Count G ≥ Nat.sqrt n

theorem erdos_problem_60 : ErdosConjecture := by
  sorry

end ErdosProblem60

end