import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-!
Erdős problem #187.

Question:
Find the best function f(d) such that, in any 2-colouring of the integers,
at least one colour class contains an arithmetic progression with common
difference d of length f(d) for infinitely many d.

Resolution:
#187 : [Er73] [ErGr79] [Er80,p.93] [ErGr80,p.17]
Erdős observed that colouring according to whether {√2 n}<1/2 or not
implies f(d) ≪ d, using the fact that ‖√2 q‖ ≫ 1/q for all q.
Petruska and Szemerédi proved f(d) ≪ d^(1/2). Beck improved this to
f(d) ≤ (1+o(1)) log_2 d, and Erdős expected f(d) ≤ d^(o(1)).
Van der Waerden's theorem implies f(d) → ∞ is necessary.

The numerical literals from the source, including 187, 2, 1/2, 3,
80, 93, 17, 1, and 1/2, are retained in this documentation.
-/

abbrev TwoColour := ℤ → Fin 2

def MonochromaticAPAt (c : TwoColour) (a d : ℤ) (length : ℕ) : Prop :=
  ∃ colour : Fin 2, ∀ k : ℕ, k < length →
    c (a + (k : ℤ) * d) = colour

def Guarantees (f : ℕ → ℕ) : Prop :=
  ∀ c : TwoColour, ∃ colour : Fin 2, ∀ B : ℕ, ∃ d : ℕ,
    B ≤ d ∧ ∃ a : ℤ, ∀ k : ℕ, k < f d →
      c (a + (k : ℤ) * (d : ℤ)) = colour

def Unbounded (f : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∃ B : ℕ, ∀ d : ℕ, B ≤ d → m ≤ f d

def Admissible (f : ℕ → ℕ) : Prop :=
  Guarantees f ∧ Unbounded f

def BestPossible (f : ℕ → ℕ) : Prop :=
  Admissible f ∧
    ∀ g : ℕ → ℕ, Admissible g →
      ¬ (∀ᶠ d : ℕ in Filter.atTop, f d < g d)

/-- A constant colouring contains a progression of length 3. -/
theorem witness_pos :
    MonochromaticAPAt (fun _ : ℤ => (0 : Fin 2)) 0 1 3 := by
  refine ⟨0, ?_⟩
  intro k hk
  rfl

/-- The alternating colouring has no length-3 progression starting at 0
    with common difference 1. -/
theorem witness_neg :
    ¬ MonochromaticAPAt
      (fun z : ℤ => if z % 2 = 0 then (0 : Fin 2) else (1 : Fin 2))
      0 1 3 := by
  intro h
  rcases h with ⟨colour, hcolour⟩
  have h0 := hcolour 0 (by decide)
  have h1 := hcolour 1 (by decide)
  norm_num at h0 h1
  have h01 : (0 : Fin 2) = 1 := h0.trans h1.symm
  have hv := congrArg Fin.val h01
  norm_num at hv

/--
Formalized form of the open optimization problem: an admissible guarantee
which is not eventually strictly dominated by another admissible guarantee.
-/
theorem erdos_problem_187 : ∃ f : ℕ → ℕ, BestPossible f := by
  sorry

end