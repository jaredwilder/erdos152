import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
open scoped Topology
open Filter

/-
Erdős problem #975.  The source records [Er65b], [Va39], [Er52b], [Ho63],
[Mc95], [Mc97], [Mc99], the example 3 / π, and n^2 + 1.  It also contains
the bibliographic numerals 0, 4, 27, 2025, 2026, 08, 30, and OEIS A147807.
-/

def divisorCount (m : ℕ) : ℕ :=
  (Nat.divisors m).card

def divisorSum (f : Polynomial ℤ) (X : ℕ) : ℕ :=
  Finset.sum (Finset.range (X + 1)) (fun n =>
    divisorCount (Int.natAbs (f.eval (n : ℤ))))

def Admissible (f : Polynomial ℤ) : Prop :=
  ∀ᶠ n : ℕ in atTop, (1 : ℤ) ≤ f.eval (n : ℤ)

def HasDivisorAsymptotic (f : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Tendsto
      (fun X : ℕ =>
        (divisorSum f X : ℝ) /
          ((X : ℝ) * Real.log (X : ℝ)))
      atTop (𝓝 c)

def Erdos975 : Prop :=
  ∀ f : Polynomial ℤ,
    Irreducible f →
    f.natDegree ≠ 0 →
    Admissible f →
    HasDivisorAsymptotic f

theorem witness_pos : Admissible (Polynomial.X + 1 : Polynomial ℤ) := by
  simp [Admissible]

theorem witness_neg : ¬ Admissible (0 : Polynomial ℤ) := by
  intro h
  have h' : ∀ᶠ n : ℕ in atTop, (1 : ℤ) ≤ 0 := by
    simpa [Admissible] using h
  rcases (eventually_atTop.1 h') with ⟨N, hN⟩
  have hbad := hN N le_rfl
  norm_num at hbad

theorem erdos_975 : Erdos975 := by
  sorry

end