import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
def ValidColoring (n : ℕ) (c : Fin n → Fin n → Bool) : Prop :=
  (∀ i : Fin n, c i i = false) ∧
    (∀ i j : Fin n, c i j = c j i)

def InjectiveFin {a n : ℕ} (f : Fin a → Fin n) : Prop :=
  ∀ i j : Fin a, f i = f j → i = j

def BlueClique (a n : ℕ) (c : Fin n → Fin n → Bool) : Prop :=
  ∃ f : Fin a → Fin n,
    InjectiveFin f ∧
      ∀ i j : Fin a, i ≠ j → c (f i) (f j) = true

def RedClique (b n : ℕ) (c : Fin n → Fin n → Bool) : Prop :=
  ∃ f : Fin b → Fin n,
    InjectiveFin f ∧
      ∀ i j : Fin b, i ≠ j → c (f i) (f j) = false

def RamseyProperty (a b n : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Bool,
    ValidColoring n c →
      BlueClique a n c ∨ RedClique b n c

noncomputable def ramseyNumber (a k : ℕ) : ℕ :=
  sInf {n : ℕ | RamseyProperty a k n}

def ramseyDifference (k : ℕ) : ℕ :=
  ramseyNumber 3 (k + 1) - ramseyNumber 3 k

def TendsToInfinity : Prop :=
  ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → M ≤ ramseyDifference k

def LittleO : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (ramseyDifference k : ℚ) ≤ ε * (k : ℚ)

theorem witness_pos : RamseyProperty 3 1 1 := by
  unfold RamseyProperty
  intro c hc
  right
  refine ⟨(fun _ : Fin 1 => (0 : Fin 1)), ?_, ?_⟩
  · intro i j h
    exact Subsingleton.elim _ _
  · intro i j h
    exfalso
    apply h
    exact Subsingleton.elim _ _

theorem witness_neg : ¬ RamseyProperty 3 3 1 := by
  intro h
  unfold RamseyProperty at h
  let c : Fin 1 → Fin 1 → Bool := fun _ _ => false
  have hc : ValidColoring 1 c := by
    constructor
    · intro i
      rfl
    · intro i j
      rfl
  have hp := h c hc
  have noinj : ∀ f : Fin 3 → Fin 1, ¬ InjectiveFin f := by
    intro f hf
    have heq : (0 : Fin 3) = 1 := hf 0 1 (Subsingleton.elim _ _)
    exact (by decide : (0 : Fin 3) ≠ 1) heq
  rcases hp with hb | hr
  · rcases hb with ⟨f, hf, hblue⟩
    exact noinj f hf
  · rcases hr with ⟨f, hf, hred⟩
    exact noinj f hf

theorem erdos_544 :
    TendsToInfinity ∧ (LittleO ∨ ¬ LittleO) := by
  sorry

end