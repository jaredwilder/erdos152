import Mathlib


noncomputable section
open scoped BigOperators
open scoped BigOperators
open scoped Topology
open Filter

/-- A bounded search space sufficient to witness progressions contained in `A`.
    The extra `2` also permits the one-term progression with common difference `1`. -/
def apBound (A : Finset ℕ) : ℕ :=
  A.sup id + 2

/-- A finite, decidable version of being the image of `range k` under an
    arithmetic progression map, with positive common difference. -/
def IsArithmeticProgression (k : ℕ) (A P : Finset ℕ) : Prop :=
  P ⊆ A ∧
    P.card = k ∧
      ∃ a ∈ Finset.range (apBound A),
        ∃ d ∈ Finset.range (apBound A),
          0 < d ∧ P = (Finset.range k).image (fun i => a + i * d)

/-- The family of `k`-term arithmetic progressions contained in `A`. -/
def arithmeticProgressions (k : ℕ) (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (fun P =>
    P.card = k ∧
      ∃ a ∈ Finset.range (apBound A),
        ∃ d ∈ Finset.range (apBound A),
          0 < d ∧ P = (Finset.range k).image (fun i => a + i * d))

def hasArithmeticProgression (k : ℕ) (A : Finset ℕ) : Prop :=
  (arithmeticProgressions k A).Nonempty

def numberOfArithmeticProgressions (k : ℕ) (A : Finset ℕ) : ℕ :=
  (arithmeticProgressions k A).card

/-- The finite-set formulation of the threshold property defining `F_k(N, ℓ)`. -/
def ThresholdProperty (k N ell t : ℕ) : Prop :=
  ∀ A : Finset ℕ,
    A.card = N →
      t ≤ numberOfArithmeticProgressions k A →
        hasArithmeticProgression ell A

/-- The threshold obtained by taking the infimum of all valid thresholds. -/
noncomputable def F (k N ell : ℕ) : ℕ :=
  sInf {t : ℕ | ThresholdProperty k N ell t}

/-- The two asymptotic assertions asked about in the problem. -/
def Erdos179Conjecture : Prop :=
  Filter.Tendsto
      (fun N : ℕ => (F 3 N 4 : ℝ) / (N : ℝ) ^ 2)
      atTop (𝓝 0) ∧
    ∀ ell : ℕ, 3 < ell →
      Filter.Tendsto
        (fun N : ℕ =>
          Real.log (F 3 N ell : ℝ) / Real.log (N : ℝ))
        atTop (𝓝 2)

theorem witness_pos :
    hasArithmeticProgression 1 ({0} : Finset ℕ) := by
  unfold hasArithmeticProgression
  refine ⟨{0}, ?_⟩
  simp only [arithmeticProgressions]
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · exact Finset.mem_powerset.mpr (by simp)
  · refine ⟨by simp, 0, by simp [apBound], 1, by simp [apBound], by simp, ?_⟩
    simp

theorem witness_neg :
    ¬ hasArithmeticProgression 2 ({0} : Finset ℕ) := by
  intro h
  unfold hasArithmeticProgression at h
  rcases h with ⟨P, hP⟩
  simp only [arithmeticProgressions, Finset.mem_filter] at hP
  have hsub : P ⊆ ({0} : Finset ℕ) :=
    Finset.mem_powerset.mp hP.1
  have hcard : P.card = 2 := hP.2.1
  have hc : P.card ≤ ({0} : Finset ℕ).card :=
    Finset.card_le_card hsub
  rw [hcard] at hc
  simpa using hc

theorem erdos_problem_179 : Erdos179Conjecture := by
  sorry

end