import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open Finset

/-- The canonical adjacency value of a graph code on a finite vertex set. -/
def adjacency {v : ℕ} (g : Fin v → Fin v → Bool)
    (a b : Fin v) : Bool :=
  if a < b then g a b else g b a

/-- The number of edges represented by a graph code. -/
def edgeCount {v : ℕ} (g : Fin v → Fin v → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin v × Fin v)).filter
    (fun e => e.1 < e.2 ∧ g e.1 e.2 = true)).card

/-- A monochromatic copy of the complete bipartite graph with parts of size `n`. -/
def hasMonochromaticBipartiteCopy (n v : ℕ)
    (g c : Fin v → Fin v → Bool) : Prop :=
  ∃ f h : Fin n → Fin v,
    Function.Injective f ∧
    Function.Injective h ∧
    (∀ i j, f i ≠ h j) ∧
    ∃ b : Bool, ∀ i j,
      adjacency g (f i) (h j) = true ∧
      adjacency c (f i) (h j) = b

/-- There is a host graph with exactly `m` edges forcing a monochromatic `K_{n,n}`.
The host is taken on `2 * m` vertices; isolated vertices can always be discarded. -/
def ramseyAt (n m : ℕ) : Prop :=
  ∃ g : Fin (2 * m) → Fin (2 * m) → Bool,
    edgeCount g = m ∧
    ∀ c : Fin (2 * m) → Fin (2 * m) → Bool,
      hasMonochromaticBipartiteCopy n (2 * m) g c

/-- The size Ramsey number, expressed as the least feasible edge count. -/
def sizeRamsey (n : ℕ) : ℕ :=
  sInf {m : ℕ | ramseyAt n m}

/-- Two-sided comparison up to constant factors. -/
def asymp (f h : ℕ → ℝ) : Prop :=
  ∃ c C N : ℝ,
    0 < c ∧ 0 < C ∧
    ∀ n : ℕ, N ≤ n →
      c * f n ≤ h n ∧ h n ≤ C * f n

theorem witness_pos : ramseyAt 1 1 := by
  let g : Fin 2 → Fin 2 → Bool :=
    fun a b => if a = 0 ∧ b = 1 then true else false
  refine ⟨g, ?_, ?_⟩
  · native_decide
  · intro c
    let f : Fin 1 → Fin 2 := fun _ => 0
    let h : Fin 1 → Fin 2 := fun _ => 1
    refine ⟨f, h, ?_, ?_, ?_, ?_⟩
    · intro i j _
      exact Subsingleton.elim _ _
    · intro i j _
      exact Subsingleton.elim _ _
    · intro i j
      simp [f, h]
    · refine ⟨adjacency c 0 1, ?_⟩
      intro i j
      simp [f, h, adjacency, g]

theorem witness_neg : ¬ ramseyAt 2 1 := by
  intro hramsey
  rcases hramsey with ⟨g, hg, hforall⟩
  let c : Fin 2 → Fin 2 → Bool := fun _ _ => false
  rcases hforall c with ⟨f, h, hf, hh, hdisj, hb⟩
  have hf0 : f 0 = (0 : Fin 2) ∨ f 0 = 1 := by
    have hx : (f 0).val < 2 := (f 0).isLt
    have hx' : (f 0).val = 0 ∨ (f 0).val = 1 := by
      omega
    rcases hx' with hx' | hx'
    · left
      apply Fin.ext
      simpa using hx'
    · right
      apply Fin.ext
      simpa using hx'
  have hf1 : f 1 = (0 : Fin 2) ∨ f 1 = 1 := by
    have hx : (f 1).val < 2 := (f 1).isLt
    have hx' : (f 1).val = 0 ∨ (f 1).val = 1 := by
      omega
    rcases hx' with hx' | hx'
    · left
      apply Fin.ext
      simpa using hx'
    · right
      apply Fin.ext
      simpa using hx'
  have hh0 : h 0 = (0 : Fin 2) ∨ h 0 = 1 := by
    have hx : (h 0).val < 2 := (h 0).isLt
    have hx' : (h 0).val = 0 ∨ (h 0).val = 1 := by
      omega
    rcases hx' with hx' | hx'
    · left
      apply Fin.ext
      simpa using hx'
    · right
      apply Fin.ext
      simpa using hx'
  have hfd : f 0 ≠ f 1 := by
    intro he
    simpa using (hf he)
  have hA : f 0 ≠ h 0 := hdisj 0 0
  have hB : f 1 ≠ h 0 := hdisj 1 0
  rcases hf0 with hf0 | hf0 <;>
    rcases hf1 with hf1 | hf1 <;>
      rcases hh0 with hh0 | hh0 <;>
        simp_all

theorem main_conjecture :
    (∀ n : ℕ, 6 ≤ n →
      (1 / 60 : ℝ) * (n : ℝ) ^ 2 * (2 : ℝ) ^ n <
        (sizeRamsey n : ℝ)) ∧
    (∀ n : ℕ,
      (sizeRamsey n : ℝ) <
        (3 / 2 : ℝ) * (n : ℝ) ^ 3 * (2 : ℝ) ^ n) ∧
    asymp
      (fun n : ℕ => (n : ℝ) ^ 3 * (2 : ℝ) ^ n)
      (fun n : ℕ => (sizeRamsey n : ℝ)) := by
  sorry

end