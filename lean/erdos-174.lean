import Mathlib

open scoped BigOperators

noncomputable section
open Classical

/-
The numerical references occurring in the source are: 174, 108, 75, 79, 80, 83,
73, 90, 92, 91, 12, 0, 4, 16, 2025, and 2026-08-30.
-/

/-- A point of Euclidean `n`-space. -/
abbrev Point (n : ℕ) := Fin n → ℝ

/-- Squared Euclidean distance. -/
def euclidSq {n : ℕ} (x y : Point n) : ℝ :=
  ∑ i, (x i - y i) ^ 2

/-- A finite point set lying on a sphere. -/
def Spherical {n : ℕ} (A : Finset (Point n)) : Prop :=
  ∃ c : Point n, ∃ r : ℝ,
    0 ≤ r ∧
      ∀ x ∈ A, euclidSq x c = r

/-- A monochromatic isometric copy of a finite configuration. -/
def MonoCopy {n d k : ℕ} (A : Finset (Point n))
    (colour : Point d → Fin k) : Prop :=
  ∃ f : Point n → Point d,
    (∀ ⦃x y⦄, x ∈ A → y ∈ A → f x = f y → x = y) ∧
      (∀ ⦃x y⦄, x ∈ A → y ∈ A →
        euclidSq (f x) (f y) = euclidSq x y) ∧
      ∃ j : Fin k, ∀ x ∈ A, colour (f x) = j

/--
The Ramsey property from the question: for every positive number of colours,
some finite-dimensional Euclidean space forces a monochromatic copy.
-/
def Ramsey {n : ℕ} (A : Finset (Point n)) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ d : ℕ, ∀ colour : Point d → Fin k, MonoCopy A colour

def p (a : ℝ) : Point 1 := fun _ => a

def singletonConfiguration : Finset (Point 1) :=
  {p 0}

def nonsphericalConfiguration : Finset (Point 1) :=
  {p 0, p 1, p 3}

/-- A one-point configuration is spherical. -/
theorem witness_pos : Spherical singletonConfiguration := by
  refine ⟨p 0, 0, by norm_num, ?_⟩
  intro x hx
  simp [singletonConfiguration] at hx
  subst x
  simp [euclidSq, p]

/-- Three suitably spaced collinear points do not lie on one sphere. -/
theorem witness_neg : ¬ Spherical nonsphericalConfiguration := by
  intro h
  rcases h with ⟨c, r, hr, hs⟩
  have h0 := hs (p 0) (by simp [nonsphericalConfiguration])
  have h1 := hs (p 1) (by simp [nonsphericalConfiguration])
  have h3 := hs (p 3) (by simp [nonsphericalConfiguration])
  simp [euclidSq, p] at h0 h1 h3
  nlinarith

/--
The characterization asked for in the problem, incorporating the known
necessary condition and the conjectured converse.
-/
theorem ramsey_iff_spherical :
    ∀ n : ℕ, ∀ A : Finset (Point n), Ramsey A ↔ Spherical A := by
  sorry