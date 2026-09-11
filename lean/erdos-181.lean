import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
abbrev CubeVertex (n : ℕ) := Fin n → Fin 2

def cubeAdjacent (n : ℕ) (x y : CubeVertex n) : Prop :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card = 1

def cubeVertexCount (n : ℕ) : ℕ :=
  2 ^ n

def cubeEdgeCount (n : ℕ) : ℕ :=
  n * 2 ^ (n - 1)

theorem cube_vertex_count (n : ℕ) :
    Fintype.card (CubeVertex n) = 2 ^ n := by
  simp [CubeVertex]

def monochromaticCopy (n N : ℕ)
    (c : Fin N → Fin N → Bool)
    (f : CubeVertex n → Fin N) : Prop :=
  Function.Injective f ∧
    ∃ b : Bool, ∀ x y : CubeVertex n,
      cubeAdjacent n x y → c (f x) (f y) = b

def ramseyProperty (n N : ℕ) : Prop :=
  ∀ c : Fin N → Fin N → Bool,
    (∀ i j : Fin N, c i j = c j i) →
      ∃ f : CubeVertex n → Fin N, monochromaticCopy n N c f

def cubeRamseyBound : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → ramseyProperty n (C * 2 ^ n)

theorem witness_pos : ramseyProperty 0 1 := by
  intro c _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro x y _
    exact Subsingleton.elim _ _
  · refine ⟨c 0 0, ?_⟩
    intro x y hxy
    exfalso
    simpa [cubeAdjacent] using hxy

theorem witness_neg : ¬ ramseyProperty 1 1 := by
  intro h
  let c : Fin 1 → Fin 1 → Bool := fun _ _ => false
  have hc : ∀ i j : Fin 1, c i j = c j i := by
    intro i j
    rfl
  obtain ⟨f, hf, _⟩ := h c hc
  let x : CubeVertex 1 := fun _ => 0
  let y : CubeVertex 1 := fun _ => 1
  have hxy : x ≠ y := by
    intro e
    have hv := congrFun e (0 : Fin 1)
    norm_num [x, y] at hv
  exact hxy (hf (Subsingleton.elim _ _))

theorem cube_ramsey_conjecture : cubeRamseyBound := by
  sorry

end