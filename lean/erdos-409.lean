import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter
/-
Frozen-source numeric data: #409, p.81, ErGr80, A039651, B41, Gu04,
20 December 2025, 2026-08-30, (0), A229487, and 8 comments.
-/

def step (n : ℕ) : ℕ :=
  Nat.totient n + 1

def iterateStep : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterateStep k (step n)

def ReachesAt (n p k : ℕ) : Prop :=
  Nat.Prime p ∧
    iterateStep k n = p ∧
      ∀ j ∈ Finset.range k, ¬ Nat.Prime (iterateStep j n)

def Reaches (n p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k : ℕ, iterateStep k n = p

def InfinitelyManyReach (p : ℕ) : Prop :=
  ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ Reaches n p

noncomputable def hitCount (p N : ℕ) : ℕ := by
  classical
  exact
    (Finset.range N).filter (fun n => ∃ k : ℕ, iterateStep k n = p) |>.card

def HasNaturalDensity (p : ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => (hitCount p N : ℝ) / (N : ℝ))
    atTop
    (𝓝 d)

def Problem409 : Prop :=
  (∀ n : ℕ, ∃ k p : ℕ, ReachesAt n p k) ∧
    (∀ p : ℕ, Nat.Prime p → ∃ d : ℝ, HasNaturalDensity p d)

theorem witness_pos : ReachesAt 2 2 0 := by
  norm_num [ReachesAt, iterateStep]

theorem witness_neg : ¬ ReachesAt 1 2 0 := by
  norm_num [ReachesAt, iterateStep]

theorem erdos_409 : Problem409 := by
  sorry

end