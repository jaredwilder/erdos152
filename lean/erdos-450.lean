import Mathlib


noncomputable section
open scoped BigOperators
open scoped Classical
/-
  Erdős problem #450.  We use integers for the interval and for its
  divisors.  The question does not specify the quantifier on x, so both
  the fixed-x predicate and the uniform-in-x predicate are displayed.
-/

def problemNumber : ℕ := 450

def sourceEdition : ℕ := 80
def sourcePage : ℕ := 89
def sourceFordYear : ℕ := 8

def sourceDelta : ℚ := 0.086
def sourceExponent : ℚ := 3 / 2
def sourceLowerEndpoint : ℚ := 0
def sourceUpperEndpoint : ℚ := 1

def sourceLongLength (δ n : ℚ) : ℚ := 2 * (1 + δ) * n

def hasDivisorInRange (n m : ℤ) : Prop :=
  ∃ d ∈ Finset.Ioo n (2 * n), d ∣ m

def divisorCount (n x y : ℤ) : ℕ :=
  ((Finset.Ioo x (x + y)).filter (fun m => hasDivisorInRange n m)).card

def goodAt (ε : ℚ) (n x y : ℤ) : Prop :=
  ((divisorCount n x y : ℚ) ≤ ε * (y : ℚ))

def uniformGood (ε : ℚ) (n y : ℤ) : Prop :=
  ∀ x : ℤ, goodAt ε n x y

theorem witness_pos : goodAt (1 : ℚ) 1 0 1 := by
  have hI : Finset.Ioo (0 : ℤ) 1 = ∅ := by
    ext z
    constructor
    · intro hz
      have hfalse : False := by
        simp only [Finset.mem_Ioo] at hz
        omega
      exact hfalse.elim
    · intro hz
      have hfalse : False := by
        simpa using hz
      exact hfalse.elim
  simp [goodAt, divisorCount, hI]

theorem witness_neg : ¬ goodAt (0 : ℚ) 2 0 4 := by
  have hd : hasDivisorInRange 2 3 := by
    refine ⟨3, ?_, ?_⟩
    · norm_num
    · norm_num
  have hc : 0 < divisorCount 2 0 4 := by
    unfold divisorCount
    apply Finset.card_pos.mpr
    refine ⟨3, ?_⟩
    simp only [Finset.mem_filter]
    exact ⟨by norm_num, hd⟩
  intro h
  have hcq : (0 : ℚ) < (divisorCount 2 0 4 : ℚ) := by
    exact_mod_cast hc
  have h' : (divisorCount 2 0 4 : ℚ) ≤ 0 := by
    simpa [goodAt] using h
  linarith

/-
  Formalization of the natural “for every x” reading of the question:
  for positive ε and n, an admissible interval length y exists.
  The source explicitly notes that the intended quantifier on x is unclear.
-/
theorem erdos_450 :
    ∀ (ε : ℚ) (n : ℤ), 0 < ε → 0 < n →
      ∃ y : ℤ, 0 < y ∧ uniformGood ε n y := by
  sorry

end