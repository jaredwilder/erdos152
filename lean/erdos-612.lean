import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic


noncomputable section
open scoped BigOperators
open scoped Classical
structure FiniteGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def FiniteGraph.Adj {n : ℕ} (G : FiniteGraph n) (u v : Fin n) : Prop :=
  G.adj u v = true

instance {n : ℕ} (G : FiniteGraph n) : DecidableRel G.Adj := by
  intro u v
  dsimp [FiniteGraph.Adj]
  infer_instance

def degree {n : ℕ} (G : FiniteGraph n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => G.adj v w = true)).card

def CliqueOn {n : ℕ} (G : FiniteGraph n) (s : Finset (Fin n)) : Prop :=
  ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v

def CliqueFree {n : ℕ} (G : FiniteGraph n) (k : ℕ) : Prop :=
  ∀ s : Finset (Fin n), s.card = k → ¬ CliqueOn G s

def lastOption {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => lastOption xs

def Chain {n : ℕ} (G : FiniteGraph n) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | u :: v :: xs => G.Adj u v ∧ Chain G (v :: xs)

def Joins {n : ℕ} (G : FiniteGraph n) (u v : Fin n) (l : List (Fin n)) : Prop :=
  l.head? = some u ∧ lastOption l = some v ∧ Chain G l

def Connected {n : ℕ} (G : FiniteGraph n) : Prop :=
  ∀ u v : Fin n, ∃ l : List (Fin n), Joins G u v l

def HasPathsOfLengthAtMost {n : ℕ} (G : FiniteGraph n) (D : ℕ) : Prop :=
  ∀ u v : Fin n, ∃ l : List (Fin n), Joins G u v l ∧ l.length ≤ D + 1

def Diameter {n : ℕ} (G : FiniteGraph n) (D : ℕ) : Prop :=
  HasPathsOfLengthAtMost G D ∧
    ∀ E : ℕ, E < D → ¬ HasPathsOfLengthAtMost G E

def EvenConjecture (r : ℕ) : Prop :=
  ∃ C : ℝ, ∀ (n d D : ℕ) (G : FiniteGraph n),
    2 ≤ r →
    Connected G →
    Diameter G D →
    0 < d →
    (r - 1) * (3 * r + 2) ∣ d →
    (∀ v : Fin n, d ≤ degree G v) →
    CliqueFree G (2 * r) →
    (D : ℝ) ≤
      (((2 : ℝ) * ((r : ℝ) - 1) * (3 * (r : ℝ) + 2)) /
        (2 * (r : ℝ) ^ 2 - 1)) * ((n : ℝ) / (d : ℝ)) + C

def OddConjecture (r : ℕ) : Prop :=
  ∃ C : ℝ, ∀ (n d D : ℕ) (G : FiniteGraph n),
    1 ≤ r →
    Connected G →
    Diameter G D →
    0 < d →
    3 * r - 1 ∣ d →
    (∀ v : Fin n, d ≤ degree G v) →
    CliqueFree G (2 * r + 1) →
    (D : ℝ) ≤
      (((3 * (r : ℝ) - 1) / (r : ℝ)) * ((n : ℝ) / (d : ℝ)) + C)

def EmptyGraph (n : ℕ) : FiniteGraph n where
  adj := fun _ _ => false
  symm := by intro u v; rfl
  loopless := by intro u; rfl

def CompleteGraph (n : ℕ) : FiniteGraph n where
  adj := fun u v => if u = v then false else true
  symm := by
    intro u v
    simp [eq_comm]
  loopless := by
    intro u
    simp

theorem witness_pos : CliqueFree (EmptyGraph 1) 2 := by
  intro s hs _
  have hle := Finset.card_le_univ s
  simp at hle
  omega

theorem witness_neg : ¬ CliqueFree (CompleteGraph 2) 2 := by
  intro h
  have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by
    simp
  have hcl : CliqueOn (CompleteGraph 2) (Finset.univ : Finset (Fin 2)) := by
    intro u hu v hv huv
    simp [FiniteGraph.Adj, CompleteGraph, huv]
  exact (h Finset.univ hcard) hcl

theorem erdos_612 :
    (∀ r : ℕ, 2 ≤ r → EvenConjecture r) ∧
    (∀ r : ℕ, 1 ≤ r → OddConjecture r) := by
  sorry

end