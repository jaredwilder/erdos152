import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/- Source numerical data retained from Erdős Problem #120:
   [Er74b] [Er81b,p.29] [Er83d] [Er90] [Er97f] [Va99,2.46],
   [St20], Problem 94, and the example A = {1, 1/2, 1/4, ...},
   whose terms converge to 0. -/

def geometricExample : Set ℝ := {1, (1 : ℝ) / 2, (1 : ℝ) / 4}

def affineImage (a b : ℝ) (A : Set ℝ) : Set ℝ :=
  {y | ∃ x, x ∈ A ∧ y = a * x + b}

def SimilarityAvoids (A E : Set ℝ) : Prop :=
  ∀ a b : ℝ, a ≠ 0 → ¬ affineImage a b A ⊆ E

def ErdősSimilarityProperty (A : Set ℝ) : Prop :=
  ∃ E : Set ℝ, 0 < MeasureTheory.volume E ∧ SimilarityAvoids A E

/-
A bounded, decidable finite analogue is used for kernel-checkable witnesses.
The carrier Fin 3 supplies a finite model of affine maps, and nonemptiness
plays the role of positive size in this finite analogue.
-/
def finiteAffineImage (a b : Fin 3) (A : Finset (Fin 3)) : Finset (Fin 3) :=
  A.image (fun x => a * x + b)

def FiniteSimilarityAvoids (A E : Finset (Fin 3)) : Prop :=
  ∀ a b : Fin 3, a ≠ 0 → ¬ finiteAffineImage a b A ⊆ E

def FiniteErdősSimilarityProperty (A E : Finset (Fin 3)) : Prop :=
  E.Nonempty ∧ FiniteSimilarityAvoids A E

theorem witness_pos :
    FiniteErdősSimilarityProperty
      ({0, 1} : Finset (Fin 3))
      ({0} : Finset (Fin 3)) := by
  constructor
  · simp
  · intro a b ha hsub
    have hbmem : b ∈ finiteAffineImage a b ({0, 1} : Finset (Fin 3)) := by
      refine Finset.mem_image.mpr ?_
      exact ⟨0, by simp, by simp⟩
    have habmem : a + b ∈ finiteAffineImage a b ({0, 1} : Finset (Fin 3)) := by
      refine Finset.mem_image.mpr ?_
      exact ⟨1, by simp, by simp⟩
    have hb0 : b = 0 := by
      have h := hsub hbmem
      simpa using h
    have hab0 : a + b = 0 := by
      have h := hsub habmem
      simpa using h
    apply ha
    calc
      a = a + 0 := by simp
      _ = a + b := by rw [hb0]
      _ = 0 := hab0

theorem witness_neg :
    ¬ FiniteErdősSimilarityProperty
      ({0, 1} : Finset (Fin 3))
      ({0, 1} : Finset (Fin 3)) := by
  intro h
  exact (h.2 (1 : Fin 3) (0 : Fin 3) (by simp)) (by
    simp [finiteAffineImage])

theorem erdos_problem_120 :
    ∀ A : Set ℝ, A.Infinite → ErdősSimilarityProperty A := by
  sorry

end