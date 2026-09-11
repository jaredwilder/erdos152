import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
structure FGraph where
  n : ℕ
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  loop : ∀ i, adj i i = false

def completeGraph (n : ℕ) : FGraph :=
  { n := n
    adj := fun i j => decide (i ≠ j)
    symm := by
      intro i j
      simp [eq_comm]
    loop := by
      intro i
      simp }

def emptyGraph : FGraph :=
  completeGraph 0

def singletonGraph : FGraph :=
  completeGraph 1

def IsColoring {n : ℕ} (c : Fin n → Fin n → Bool) : Prop :=
  (∀ i j, c i j = c j i) ∧ (∀ i, c i i = false)

def ContainsMonochromatic {n N : ℕ} (G : FGraph)
    (c : Fin N → Fin N → Bool) (e : Fin G.n → Fin N) (colour : Bool) : Prop :=
  Function.Injective e ∧
    ∀ i j, G.adj i j = true → c (e i) (e j) = colour

def RamseyProperty (G : FGraph) (N : ℕ) : Prop :=
  ∀ c : Fin N → Fin N → Bool,
    IsColoring c →
      ∃ e : Fin G.n → Fin N,
        ContainsMonochromatic (n := G.n) G c e false ∨
          ContainsMonochromatic (n := G.n) G c e true

noncomputable def ramseyNumber (G : FGraph) : ℕ :=
  sInf {N : ℕ | RamseyProperty G N}

def Colorable (G : FGraph) (k : ℕ) : Prop :=
  ∃ c : Fin G.n → Fin k,
    ∀ i j, G.adj i j = true → c i ≠ c j

noncomputable def chromaticNumber (G : FGraph) : ℕ :=
  sInf {k : ℕ | Colorable G k}

def FirstClaim : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ G : FGraph, chromaticNumber G = k →
        (1 - ε) ^ k * (ramseyNumber (completeGraph k) : ℝ) <
          (ramseyNumber G : ℝ)

def StrongerClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ G : FGraph, chromaticNumber G = k →
        c * (ramseyNumber (completeGraph k) : ℝ) <
          (ramseyNumber G : ℝ)

def originalSmallCase : ℕ := 3

def trivialEpsilonThreshold : ℝ := 3 / 4

def pentagonalWheelRamseyValue : ℕ := 17

def sourceRamseyUpperBound (k : ℕ) : ℕ := 4 ^ k

def sourceRandomColouringScale (k : ℕ) : ℝ := 2 ^ (k / 2)

def sourceHalf : ℝ := 1 / 2

theorem witness_pos : RamseyProperty emptyGraph 0 := by
  intro c hc
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  left
  constructor
  · intro i j hij
    exact Fin.elim0 i
  · intro i j hij
    exact Fin.elim0 i

theorem witness_neg : ¬ RamseyProperty singletonGraph 0 := by
  intro h
  let c : Fin 0 → Fin 0 → Bool := fun i j => Fin.elim0 i
  have hc : IsColoring c := by
    constructor
    · intro i j
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  obtain ⟨e, _⟩ := h c hc
  let i : Fin singletonGraph.n := ⟨0, by simp [singletonGraph, completeGraph]⟩
  exact Fin.elim0 (e i)

theorem formalized_problem : (¬ FirstClaim) ∧ StrongerClaim := by
  sorry

end